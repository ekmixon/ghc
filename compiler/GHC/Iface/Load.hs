{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998

-}

{-# LANGUAGE BangPatterns, NondecreasingIndentation #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Loading interface files
module GHC.Iface.Load (
        -- Importing one thing
        tcLookupImported_maybe, importDecl,
        checkWiredInTyCon, ifCheckWiredInThing,

        -- RnM/TcM functions
        loadModuleInterface, loadModuleInterfaces,
        loadSrcInterface, loadSrcInterface_maybe,
        loadInterfaceForName, loadInterfaceForNameMaybe, loadInterfaceForModule,

        -- IfM functions
        loadInterface,
        loadSysInterface, loadUserInterface, loadPluginInterface,
        findAndReadIface, readIface, writeIface,
        moduleFreeHolesPrecise,
        needWiredInHomeIface, loadWiredInHomeIface,

        pprModIfaceSimple,
        ifaceStats, pprModIface, showIface,

        module Iface_Errors -- avoids boot files in Ppr modules
   ) where

import GHC.Prelude

import GHC.Platform.Profile

import {-# SOURCE #-} GHC.IfaceToCore
   ( tcIfaceDecls, tcIfaceRules, tcIfaceInst, tcIfaceFamInst
   , tcIfaceAnnotations, tcIfaceCompleteMatches )

import GHC.Driver.Config.Finder
import GHC.Driver.Env
import GHC.Driver.Errors.Types
import GHC.Driver.Session
import GHC.Driver.Backend
import GHC.Driver.Hooks
import GHC.Driver.Plugins

import GHC.Iface.Syntax
import GHC.Iface.Ext.Fields
import GHC.Iface.Binary
import GHC.Iface.Rename
import GHC.Iface.Env
import GHC.Iface.Errors as Iface_Errors

import GHC.Tc.Errors.Types
import GHC.Tc.Utils.Monad

import GHC.Utils.Binary   ( BinData(..) )
import GHC.Utils.Error
import GHC.Utils.Outputable as Outputable
import GHC.Utils.Panic
import GHC.Utils.Panic.Plain
import GHC.Utils.Constants (debugIsOn)
import GHC.Utils.Logger
import GHC.Utils.Trace

import GHC.Settings.Constants

import GHC.Builtin.Names
import GHC.Builtin.Utils
import GHC.Builtin.PrimOps    ( allThePrimOps, primOpFixity, primOpOcc )

import GHC.Core.Rules
import GHC.Core.TyCon
import GHC.Core.InstEnv
import GHC.Core.FamInstEnv

import GHC.Types.Id.Make      ( seqId )
import GHC.Types.Annotations
import GHC.Types.Name
import GHC.Types.Name.Cache
import GHC.Types.Name.Env
import GHC.Types.Avail
import GHC.Types.Fixity
import GHC.Types.Fixity.Env
import GHC.Types.SourceError
import GHC.Types.SourceText
import GHC.Types.SourceFile
import GHC.Types.SafeHaskell
import GHC.Types.TypeEnv
import GHC.Types.Unique.FM
import GHC.Types.Unique.DSet
import GHC.Types.SrcLoc
import GHC.Types.TyThing

import GHC.Unit.External
import GHC.Unit.Module
import GHC.Unit.Module.Warnings
import GHC.Unit.Module.ModIface
import GHC.Unit.Module.Deps
import GHC.Unit.State
import GHC.Unit.Home
import GHC.Unit.Home.ModInfo
import GHC.Unit.Finder
import GHC.Unit.Env ( ue_hpt )

import GHC.Data.Maybe
import GHC.Data.FastString

import Control.Monad
import Data.Map ( toList )
import System.FilePath
import System.Directory

{-
************************************************************************
*                                                                      *
*      tcImportDecl is the key function for "faulting in"              *
*      imported things
*                                                                      *
************************************************************************

The main idea is this.  We are chugging along type-checking source code, and
find a reference to GHC.Base.map.  We call tcLookupGlobal, which doesn't find
it in the EPS type envt.  So it
        1 loads GHC.Base.hi
        2 gets the decl for GHC.Base.map
        3 typechecks it via tcIfaceDecl
        4 and adds it to the type env in the EPS

Note that DURING STEP 4, we may find that map's type mentions a type
constructor that also

Notice that for imported things we read the current version from the EPS
mutable variable.  This is important in situations like
        ...$(e1)...$(e2)...
where the code that e1 expands to might import some defns that
also turn out to be needed by the code that e2 expands to.
-}

tcLookupImported_maybe :: Name -> TcM (MaybeErr SDoc TyThing)
-- Returns (Failed err) if we can't find the interface file for the thing
tcLookupImported_maybe name
  = do  { hsc_env <- getTopEnv
        ; mb_thing <- liftIO (lookupType hsc_env name)
        ; case mb_thing of
            Just thing -> return (Succeeded thing)
            Nothing    -> tcImportDecl_maybe name }

tcImportDecl_maybe :: Name -> TcM (MaybeErr SDoc TyThing)
-- Entry point for *source-code* uses of importDecl
tcImportDecl_maybe name
  | Just thing <- wiredInNameTyThing_maybe name
  = do  { when (needWiredInHomeIface thing)
               (initIfaceTcRn (loadWiredInHomeIface name))
                -- See Note [Loading instances for wired-in things]
        ; return (Succeeded thing) }
  | otherwise
  = initIfaceTcRn (importDecl name)

importDecl :: Name -> IfM lcl (MaybeErr SDoc TyThing)
-- Get the TyThing for this Name from an interface file
-- It's not a wired-in thing -- the caller caught that
importDecl name
  = assert (not (isWiredInName name)) $
    do  { logger <- getLogger
        ; liftIO $ trace_if logger nd_doc

        -- Load the interface, which should populate the PTE
        ; mb_iface <- assertPpr (isExternalName name) (ppr name) $
                      loadInterface nd_doc (nameModule name) ImportBySystem
        ; case mb_iface of {
                Failed err_msg  -> return (Failed err_msg) ;
                Succeeded _ -> do

        -- Now look it up again; this time we should find it
        { eps <- getEps
        ; case lookupTypeEnv (eps_PTE eps) name of
            Just thing -> return $ Succeeded thing
            Nothing    -> let doc = whenPprDebug (found_things_msg eps $$ empty)
                                    $$ not_found_msg
                          in return $ Failed doc
    }}}
  where
    nd_doc = text "Need decl for" <+> ppr name
    not_found_msg = hang (text "Can't find interface-file declaration for" <+>
                                pprNameSpace (nameNameSpace name) <+> ppr name)
                       2 (vcat [text "Probable cause: bug in .hi-boot file, or inconsistent .hi file",
                                text "Use -ddump-if-trace to get an idea of which file caused the error"])
    found_things_msg eps =
        hang (text "Found the following declarations in" <+> ppr (nameModule name) <> colon)
           2 (vcat (map ppr $ filter is_interesting $ nameEnvElts $ eps_PTE eps))
      where
        is_interesting thing = nameModule name == nameModule (getName thing)


{-
************************************************************************
*                                                                      *
           Checks for wired-in things
*                                                                      *
************************************************************************

Note [Loading instances for wired-in things]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We need to make sure that we have at least *read* the interface files
for any module with an instance decl or RULE that we might want.

* If the instance decl is an orphan, we have a whole separate mechanism
  (loadOrphanModules)

* If the instance decl is not an orphan, then the act of looking at the
  TyCon or Class will force in the defining module for the
  TyCon/Class, and hence the instance decl

* BUT, if the TyCon is a wired-in TyCon, we don't really need its interface;
  but we must make sure we read its interface in case it has instances or
  rules.  That is what GHC.Iface.Load.loadWiredInHomeIface does.  It's called
  from GHC.IfaceToCore.{tcImportDecl, checkWiredInTyCon, ifCheckWiredInThing}

* HOWEVER, only do this for TyCons.  There are no wired-in Classes.  There
  are some wired-in Ids, but we don't want to load their interfaces. For
  example, Control.Exception.Base.recSelError is wired in, but that module
  is compiled late in the base library, and we don't want to force it to
  load before it's been compiled!

All of this is done by the type checker. The renamer plays no role.
(It used to, but no longer.)
-}

checkWiredInTyCon :: TyCon -> TcM ()
-- Ensure that the home module of the TyCon (and hence its instances)
-- are loaded. See Note [Loading instances for wired-in things]
-- It might not be a wired-in tycon (see the calls in GHC.Tc.Utils.Unify),
-- in which case this is a no-op.
checkWiredInTyCon tc
  | not (isWiredInName tc_name)
  = return ()
  | otherwise
  = do  { mod <- getModule
        ; logger <- getLogger
        ; liftIO $ trace_if logger (text "checkWiredInTyCon" <+> ppr tc_name $$ ppr mod)
        ; assert (isExternalName tc_name )
          when (mod /= nameModule tc_name)
               (initIfaceTcRn (loadWiredInHomeIface tc_name))
                -- Don't look for (non-existent) Float.hi when
                -- compiling Float.hs, which mentions Float of course
                -- A bit yukky to call initIfaceTcRn here
        }
  where
    tc_name = tyConName tc

ifCheckWiredInThing :: TyThing -> IfL ()
-- Even though we are in an interface file, we want to make
-- sure the instances of a wired-in thing are loaded (imagine f :: Double -> Double)
-- Ditto want to ensure that RULES are loaded too
-- See Note [Loading instances for wired-in things]
ifCheckWiredInThing thing
  = do  { mod <- getIfModule
                -- Check whether we are typechecking the interface for this
                -- very module.  E.g when compiling the base library in --make mode
                -- we may typecheck GHC.Base.hi. At that point, GHC.Base is not in
                -- the HPT, so without the test we'll demand-load it into the PIT!
                -- C.f. the same test in checkWiredInTyCon above
        ; let name = getName thing
        ; assertPpr (isExternalName name) (ppr name) $
          when (needWiredInHomeIface thing && mod /= nameModule name)
               (loadWiredInHomeIface name) }

needWiredInHomeIface :: TyThing -> Bool
-- Only for TyCons; see Note [Loading instances for wired-in things]
needWiredInHomeIface (ATyCon {}) = True
needWiredInHomeIface _           = False


{-
************************************************************************
*                                                                      *
        loadSrcInterface, loadOrphanModules, loadInterfaceForName

                These three are called from TcM-land
*                                                                      *
************************************************************************
-}

-- | Load the interface corresponding to an @import@ directive in
-- source code.  On a failure, fail in the monad with an error message.
loadSrcInterface :: SDoc
                 -> ModuleName
                 -> IsBootInterface     -- {-# SOURCE #-} ?
                 -> Maybe FastString    -- "package", if any
                 -> RnM ModIface

loadSrcInterface doc mod want_boot maybe_pkg
  = do { res <- loadSrcInterface_maybe doc mod want_boot maybe_pkg
       ; case res of
           Failed err      -> failWithTc (TcRnUnknownMessage $ mkPlainError noHints err)
           Succeeded iface -> return iface }

-- | Like 'loadSrcInterface', but returns a 'MaybeErr'.
loadSrcInterface_maybe :: SDoc
                       -> ModuleName
                       -> IsBootInterface     -- {-# SOURCE #-} ?
                       -> Maybe FastString    -- "package", if any
                       -> RnM (MaybeErr SDoc ModIface)

loadSrcInterface_maybe doc mod want_boot maybe_pkg
  -- We must first find which Module this import refers to.  This involves
  -- calling the Finder, which as a side effect will search the filesystem
  -- and create a ModLocation.  If successful, loadIface will read the
  -- interface; it will call the Finder again, but the ModLocation will be
  -- cached from the first search.
  = do hsc_env <- getTopEnv
       let fc = hsc_FC hsc_env
       let dflags = hsc_dflags hsc_env
       let fopts = initFinderOpts dflags
       let units = hsc_units hsc_env
       let home_unit = hsc_home_unit hsc_env
       res <- liftIO $ findImportedModule fc fopts units home_unit mod maybe_pkg
       case res of
           Found _ mod -> initIfaceTcRn $ loadInterface doc mod (ImportByUser want_boot)
           -- TODO: Make sure this error message is good
           err         -> return (Failed (cannotFindModule hsc_env mod err))

-- | Load interface directly for a fully qualified 'Module'.  (This is a fairly
-- rare operation, but in particular it is used to load orphan modules
-- in order to pull their instances into the global package table and to
-- handle some operations in GHCi).
loadModuleInterface :: SDoc -> Module -> TcM ModIface
loadModuleInterface doc mod = initIfaceTcRn (loadSysInterface doc mod)

-- | Load interfaces for a collection of modules.
loadModuleInterfaces :: SDoc -> [Module] -> TcM ()
loadModuleInterfaces doc mods
  | null mods = return ()
  | otherwise = initIfaceTcRn (mapM_ load mods)
  where
    load mod = loadSysInterface (doc <+> parens (ppr mod)) mod

-- | Loads the interface for a given Name.
-- Should only be called for an imported name;
-- otherwise loadSysInterface may not find the interface
loadInterfaceForName :: SDoc -> Name -> TcRn ModIface
loadInterfaceForName doc name
  = do { when debugIsOn $  -- Check pre-condition
         do { this_mod <- getModule
            ; massertPpr (not (nameIsLocalOrFrom this_mod name)) (ppr name <+> parens doc) }
      ; assertPpr (isExternalName name) (ppr name) $
        initIfaceTcRn $ loadSysInterface doc (nameModule name) }

-- | Only loads the interface for external non-local names.
loadInterfaceForNameMaybe :: SDoc -> Name -> TcRn (Maybe ModIface)
loadInterfaceForNameMaybe doc name
  = do { this_mod <- getModule
       ; if nameIsLocalOrFrom this_mod name || not (isExternalName name)
         then return Nothing
         else Just <$> (initIfaceTcRn $ loadSysInterface doc (nameModule name))
       }

-- | Loads the interface for a given Module.
loadInterfaceForModule :: SDoc -> Module -> TcRn ModIface
loadInterfaceForModule doc m
  = do
    -- Should not be called with this module
    when debugIsOn $ do
      this_mod <- getModule
      massertPpr (this_mod /= m) (ppr m <+> parens doc)
    initIfaceTcRn $ loadSysInterface doc m

{-
*********************************************************
*                                                      *
                loadInterface

        The main function to load an interface
        for an imported module, and put it in
        the External Package State
*                                                      *
*********************************************************
-}

-- | An 'IfM' function to load the home interface for a wired-in thing,
-- so that we're sure that we see its instance declarations and rules
-- See Note [Loading instances for wired-in things]
loadWiredInHomeIface :: Name -> IfM lcl ()
loadWiredInHomeIface name
  = assert (isWiredInName name) $
    do _ <- loadSysInterface doc (nameModule name); return ()
  where
    doc = text "Need home interface for wired-in thing" <+> ppr name

------------------
-- | Loads a system interface and throws an exception if it fails
loadSysInterface :: SDoc -> Module -> IfM lcl ModIface
loadSysInterface doc mod_name = loadInterfaceWithException doc mod_name ImportBySystem

------------------
-- | Loads a user interface and throws an exception if it fails. The first parameter indicates
-- whether we should import the boot variant of the module
loadUserInterface :: IsBootInterface -> SDoc -> Module -> IfM lcl ModIface
loadUserInterface is_boot doc mod_name
  = loadInterfaceWithException doc mod_name (ImportByUser is_boot)

loadPluginInterface :: SDoc -> Module -> IfM lcl ModIface
loadPluginInterface doc mod_name
  = loadInterfaceWithException doc mod_name ImportByPlugin

------------------
-- | A wrapper for 'loadInterface' that throws an exception if it fails
loadInterfaceWithException :: SDoc -> Module -> WhereFrom -> IfM lcl ModIface
loadInterfaceWithException doc mod_name where_from
  = do
    dflags <- getDynFlags
    let ctx = initSDocContext dflags defaultUserStyle
    withException ctx (loadInterface doc mod_name where_from)

------------------
loadInterface :: SDoc -> Module -> WhereFrom
              -> IfM lcl (MaybeErr SDoc ModIface)

-- loadInterface looks in both the HPT and PIT for the required interface
-- If not found, it loads it, and puts it in the PIT (always).

-- If it can't find a suitable interface file, we
--      a) modify the PackageIfaceTable to have an empty entry
--              (to avoid repeated complaints)
--      b) return (Left message)
--
-- It's not necessarily an error for there not to be an interface
-- file -- perhaps the module has changed, and that interface
-- is no longer used

loadInterface doc_str mod from
  | isHoleModule mod
  -- Hole modules get special treatment
  = do hsc_env <- getTopEnv
       let home_unit = hsc_home_unit hsc_env
       -- Redo search for our local hole module
       loadInterface doc_str (mkHomeModule home_unit (moduleName mod)) from
  | otherwise
  = do
    logger <- getLogger
    withTimingSilent logger (text "loading interface") (pure ()) $ do
        {       -- Read the state
          (eps,hpt) <- getEpsAndHpt
        ; gbl_env <- getGblEnv

        ; liftIO $ trace_if logger (text "Considering whether to load" <+> ppr mod <+> ppr from)

                -- Check whether we have the interface already
        ; hsc_env <- getTopEnv
        ; let home_unit = hsc_home_unit hsc_env
        ; case lookupIfaceByModule hpt (eps_PIT eps) mod of {
            Just iface
                -> return (Succeeded iface) ;   -- Already loaded
                        -- The (src_imp == mi_boot iface) test checks that the already-loaded
                        -- interface isn't a boot iface.  This can conceivably happen,
                        -- if an earlier import had a before we got to real imports.   I think.
            _ -> do {

        -- READ THE MODULE IN
        ; read_result <- case (wantHiBootFile home_unit eps mod from) of
                           Failed err             -> return (Failed err)
                           Succeeded hi_boot_file -> do
                             hsc_env <- getTopEnv
                             liftIO $ computeInterface hsc_env doc_str hi_boot_file mod
        ; case read_result of {
            Failed err -> do
                { let fake_iface = emptyFullModIface mod

                ; updateEps_ $ \eps ->
                        eps { eps_PIT = extendModuleEnv (eps_PIT eps) (mi_module fake_iface) fake_iface }
                        -- Not found, so add an empty iface to
                        -- the EPS map so that we don't look again

                ; return (Failed err) } ;

        -- Found and parsed!
        -- We used to have a sanity check here that looked for:
        --  * System importing ..
        --  * a home package module ..
        --  * that we know nothing about (mb_dep == Nothing)!
        --
        -- But this is no longer valid because thNameToGhcName allows users to
        -- cause the system to load arbitrary interfaces (by supplying an appropriate
        -- Template Haskell original-name).
            Succeeded (iface, loc) ->
        let
            loc_doc = text loc
        in
        initIfaceLcl (mi_semantic_module iface) loc_doc (mi_boot iface) $

        dontLeakTheHPT $ do

        --      Load the new ModIface into the External Package State
        -- Even home-package interfaces loaded by loadInterface
        --      (which only happens in OneShot mode; in Batch/Interactive
        --      mode, home-package modules are loaded one by one into the HPT)
        -- are put in the EPS.
        --
        -- The main thing is to add the ModIface to the PIT, but
        -- we also take the
        --      IfaceDecls, IfaceClsInst, IfaceFamInst, IfaceRules,
        -- out of the ModIface and put them into the big EPS pools

        -- NB: *first* we do tcIfaceDecls, so that the provenance of all the locally-defined
        ---    names is done correctly (notably, whether this is an .hi file or .hi-boot file).
        --     If we do loadExport first the wrong info gets into the cache (unless we
        --      explicitly tag each export which seems a bit of a bore)

        ; ignore_prags      <- goptM Opt_IgnoreInterfacePragmas
        ; new_eps_decls     <- tcIfaceDecls ignore_prags (mi_decls iface)
        ; new_eps_insts     <- mapM tcIfaceInst (mi_insts iface)
        ; new_eps_fam_insts <- mapM tcIfaceFamInst (mi_fam_insts iface)
        ; new_eps_rules     <- tcIfaceRules ignore_prags (mi_rules iface)
        ; new_eps_anns      <- tcIfaceAnnotations (mi_anns iface)
        ; new_eps_complete_matches <- tcIfaceCompleteMatches (mi_complete_matches iface)

        ; let { final_iface = iface {
                                mi_decls     = panic "No mi_decls in PIT",
                                mi_insts     = panic "No mi_insts in PIT",
                                mi_fam_insts = panic "No mi_fam_insts in PIT",
                                mi_rules     = panic "No mi_rules in PIT",
                                mi_anns      = panic "No mi_anns in PIT"
                              }
               }

        ; let bad_boot = mi_boot iface == IsBoot && fmap fst (if_rec_types gbl_env) == Just mod
                            -- Warn against an EPS-updating import
                            -- of one's own boot file! (one-shot only)
                            -- See Note [Loading your own hi-boot file]

        ; warnPprTrace bad_boot (ppr mod) $
          updateEps_  $ \ eps ->
           if elemModuleEnv mod (eps_PIT eps) || is_external_sig home_unit iface
                then eps
           else if bad_boot
                -- See Note [Loading your own hi-boot file]
                then eps { eps_PTE = addDeclsToPTE (eps_PTE eps) new_eps_decls }
           else
                eps {
                  eps_PIT          = extendModuleEnv (eps_PIT eps) mod final_iface,
                  eps_PTE          = addDeclsToPTE   (eps_PTE eps) new_eps_decls,
                  eps_rule_base    = extendRuleBaseList (eps_rule_base eps)
                                                        new_eps_rules,
                  eps_complete_matches
                                   = eps_complete_matches eps ++ new_eps_complete_matches,
                  eps_inst_env     = extendInstEnvList (eps_inst_env eps)
                                                       new_eps_insts,
                  eps_fam_inst_env = extendFamInstEnvList (eps_fam_inst_env eps)
                                                          new_eps_fam_insts,
                  eps_ann_env      = extendAnnEnvList (eps_ann_env eps)
                                                      new_eps_anns,
                  eps_mod_fam_inst_env
                                   = let
                                       fam_inst_env =
                                         extendFamInstEnvList emptyFamInstEnv
                                                              new_eps_fam_insts
                                     in
                                     extendModuleEnv (eps_mod_fam_inst_env eps)
                                                     mod
                                                     fam_inst_env,
                  eps_stats        = addEpsInStats (eps_stats eps)
                                                   (length new_eps_decls)
                                                   (length new_eps_insts)
                                                   (length new_eps_rules) }

        ; -- invoke plugins with *full* interface, not final_iface, to ensure
          -- that plugins have access to declarations, etc.
          res <- withPlugins hsc_env (\p -> interfaceLoadAction p) iface
        ; return (Succeeded res)
    }}}}

{- Note [Loading your own hi-boot file]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Generally speaking, when compiling module M, we should not
load M.hi boot into the EPS.  After all, we are very shortly
going to have full information about M.  Moreover, see
Note [Do not update EPS with your own hi-boot] in GHC.Iface.Recomp.

But there is a HORRIBLE HACK here.

* At the end of tcRnImports, we call checkFamInstConsistency to
  check consistency of imported type-family instances
  See Note [The type family instance consistency story] in GHC.Tc.Instance.Family

* Alas, those instances may refer to data types defined in M,
  if there is a M.hs-boot.

* And that means we end up loading M.hi-boot, because those
  data types are not yet in the type environment.

But in this weird case, /all/ we need is the types. We don't need
instances, rules etc.  And if we put the instances in the EPS
we get "duplicate instance" warnings when we compile the "real"
instance in M itself.  Hence the strange business of just updateing
the eps_PTE.

This really happens in practice.  The module "GHC.Hs.Expr" gets
"duplicate instance" errors if this hack is not present.

This is a mess.


Note [HPT space leak] (#15111)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In IfL, we defer some work until it is demanded using forkM, such
as building TyThings from IfaceDecls. These thunks are stored in
the ExternalPackageState, and they might never be poked.  If we're
not careful, these thunks will capture the state of the loaded
program when we read an interface file, and retain all that data
for ever.

Therefore, when loading a package interface file , we use a "clean"
version of the HscEnv with all the data about the currently loaded
program stripped out. Most of the fields can be panics because
we'll never read them, but hsc_HPT needs to be empty because this
interface will cause other interfaces to be loaded recursively, and
when looking up those interfaces we use the HPT in loadInterface.
We know that none of the interfaces below here can refer to
home-package modules however, so it's safe for the HPT to be empty.
-}

dontLeakTheHPT :: IfL a -> IfL a
dontLeakTheHPT thing_inside = do
  let
    cleanTopEnv hsc_env =
       let
         -- wrinkle: when we're typechecking in --backpack mode, the
         -- instantiation of a signature might reside in the HPT, so
         -- this case breaks the assumption that EPS interfaces only
         -- refer to other EPS interfaces. We can detect when we're in
         -- typechecking-only mode by using backend==NoBackend, and
         -- in that case we don't empty the HPT.  (admittedly this is
         -- a bit of a hack, better suggestions welcome). A number of
         -- tests in testsuite/tests/backpack break without this
         -- tweak.
         old_unit_env = hsc_unit_env hsc_env
         !unit_env
          | NoBackend <- backend (hsc_dflags hsc_env)
          = old_unit_env
          | otherwise
          = old_unit_env
             { ue_hpt = emptyHomePackageTable
             }
       in
       hsc_env {  hsc_targets      = panic "cleanTopEnv: hsc_targets"
               ,  hsc_mod_graph    = panic "cleanTopEnv: hsc_mod_graph"
               ,  hsc_IC           = panic "cleanTopEnv: hsc_IC"
               ,  hsc_unit_env     = unit_env
               }

  updTopEnv cleanTopEnv $ do
  !_ <- getTopEnv        -- force the updTopEnv
  thing_inside


-- | Returns @True@ if a 'ModIface' comes from an external package.
-- In this case, we should NOT load it into the EPS; the entities
-- should instead come from the local merged signature interface.
is_external_sig :: HomeUnit -> ModIface -> Bool
is_external_sig home_unit iface =
    -- It's a signature iface...
    mi_semantic_module iface /= mi_module iface &&
    -- and it's not from the local package
    not (isHomeModule home_unit (mi_module iface))

-- | This is an improved version of 'findAndReadIface' which can also
-- handle the case when a user requests @p[A=<B>]:M@ but we only
-- have an interface for @p[A=<A>]:M@ (the indefinite interface.
-- If we are not trying to build code, we load the interface we have,
-- *instantiating it* according to how the holes are specified.
-- (Of course, if we're actually building code, this is a hard error.)
--
-- In the presence of holes, 'computeInterface' has an important invariant:
-- to load module M, its set of transitively reachable requirements must
-- have an up-to-date local hi file for that requirement.  Note that if
-- we are loading the interface of a requirement, this does not
-- apply to the requirement itself; e.g., @p[A=<A>]:A@ does not require
-- A.hi to be up-to-date (and indeed, we MUST NOT attempt to read A.hi, unless
-- we are actually typechecking p.)
computeInterface
  :: HscEnv
  -> SDoc
  -> IsBootInterface
  -> Module
  -> IO (MaybeErr SDoc (ModIface, FilePath))
computeInterface hsc_env doc_str hi_boot_file mod0 = do
  massert (not (isHoleModule mod0))
  let name_cache = hsc_NC hsc_env
  let fc         = hsc_FC hsc_env
  let home_unit  = hsc_home_unit hsc_env
  let units      = hsc_units hsc_env
  let dflags     = hsc_dflags hsc_env
  let logger     = hsc_logger hsc_env
  let hooks      = hsc_hooks hsc_env
  let find_iface m = findAndReadIface logger name_cache fc hooks units home_unit dflags doc_str
                                      m mod0 hi_boot_file
  case getModuleInstantiation mod0 of
      (imod, Just indef) | isHomeUnitIndefinite home_unit ->
        find_iface imod >>= \case
          Succeeded (iface0, path) ->
            rnModIface hsc_env (instUnitInsts (moduleUnit indef)) Nothing iface0 >>= \case
              Right x   -> return (Succeeded (x, path))
              Left errs -> throwErrors (GhcTcRnMessage <$> errs)
          Failed err -> return (Failed err)
      (mod, _) -> find_iface mod

-- | Compute the signatures which must be compiled in order to
-- load the interface for a 'Module'.  The output of this function
-- is always a subset of 'moduleFreeHoles'; it is more precise
-- because in signature @p[A=\<A>,B=\<B>]:B@, although the free holes
-- are A and B, B might not depend on A at all!
--
-- If this is invoked on a signature, this does NOT include the
-- signature itself; e.g. precise free module holes of
-- @p[A=\<A>,B=\<B>]:B@ never includes B.
moduleFreeHolesPrecise
    :: SDoc -> Module
    -> TcRnIf gbl lcl (MaybeErr SDoc (UniqDSet ModuleName))
moduleFreeHolesPrecise doc_str mod
 | moduleIsDefinite mod = return (Succeeded emptyUniqDSet)
 | otherwise =
   case getModuleInstantiation mod of
    (imod, Just indef) -> do
        logger <- getLogger
        let insts = instUnitInsts (moduleUnit indef)
        liftIO $ trace_if logger (text "Considering whether to load" <+> ppr mod <+>
                 text "to compute precise free module holes")
        (eps, hpt) <- getEpsAndHpt
        case tryEpsAndHpt eps hpt `firstJust` tryDepsCache eps imod insts of
            Just r -> return (Succeeded r)
            Nothing -> readAndCache imod insts
    (_, Nothing) -> return (Succeeded emptyUniqDSet)
  where
    tryEpsAndHpt eps hpt =
        fmap mi_free_holes (lookupIfaceByModule hpt (eps_PIT eps) mod)
    tryDepsCache eps imod insts =
        case lookupInstalledModuleEnv (eps_free_holes eps) imod of
            Just ifhs  -> Just (renameFreeHoles ifhs insts)
            _otherwise -> Nothing
    readAndCache imod insts = do
        hsc_env <- getTopEnv
        let nc        = hsc_NC hsc_env
        let fc        = hsc_FC hsc_env
        let home_unit = hsc_home_unit hsc_env
        let units     = hsc_units hsc_env
        let dflags    = hsc_dflags hsc_env
        let logger    = hsc_logger hsc_env
        let hooks     = hsc_hooks hsc_env
        mb_iface <- liftIO $ findAndReadIface logger nc fc hooks units home_unit dflags
                                              (text "moduleFreeHolesPrecise" <+> doc_str)
                                              imod mod NotBoot
        case mb_iface of
            Succeeded (iface, _) -> do
                let ifhs = mi_free_holes iface
                -- Cache it
                updateEps_ (\eps ->
                    eps { eps_free_holes = extendInstalledModuleEnv (eps_free_holes eps) imod ifhs })
                return (Succeeded (renameFreeHoles ifhs insts))
            Failed err -> return (Failed err)

wantHiBootFile :: HomeUnit -> ExternalPackageState -> Module -> WhereFrom
               -> MaybeErr SDoc IsBootInterface
-- Figure out whether we want Foo.hi or Foo.hi-boot
wantHiBootFile home_unit eps mod from
  = case from of
       ImportByUser usr_boot
          | usr_boot == IsBoot && notHomeModule home_unit mod
          -> Failed (badSourceImport mod)
          | otherwise -> Succeeded usr_boot

       ImportByPlugin
          -> Succeeded NotBoot

       ImportBySystem
          | notHomeModule home_unit mod
          -> Succeeded NotBoot
             -- If the module to be imported is not from this package
             -- don't look it up in eps_is_boot, because that is keyed
             -- on the ModuleName of *home-package* modules only.
             -- We never import boot modules from other packages!

          | otherwise
          -> case lookupUFM (eps_is_boot eps) (moduleName mod) of
                Just (GWIB { gwib_isBoot = is_boot }) ->
                  Succeeded is_boot
                Nothing ->
                  Succeeded NotBoot
                     -- The boot-ness of the requested interface,
                     -- based on the dependencies in directly-imported modules

badSourceImport :: Module -> SDoc
badSourceImport mod
  = hang (text "You cannot {-# SOURCE #-} import a module from another package")
       2 (text "but" <+> quotes (ppr mod) <+> text "is from package"
          <+> quotes (ppr (moduleUnit mod)))

-----------------------------------------------------
--      Loading type/class/value decls
-- We pass the full Module name here, replete with
-- its package info, so that we can build a Name for
-- each binder with the right package info in it
-- All subsequent lookups, including crucially lookups during typechecking
-- the declaration itself, will find the fully-glorious Name
--
-- We handle ATs specially.  They are not main declarations, but also not
-- implicit things (in particular, adding them to `implicitTyThings' would mess
-- things up in the renaming/type checking of source programs).
-----------------------------------------------------

addDeclsToPTE :: PackageTypeEnv -> [(Name,TyThing)] -> PackageTypeEnv
addDeclsToPTE pte things = extendNameEnvList pte things

{-
*********************************************************
*                                                      *
\subsection{Reading an interface file}
*                                                      *
*********************************************************

Note [Home module load error]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If the sought-for interface is in the current package (as determined
by -package-name flag) then it jolly well should already be in the HPT
because we process home-package modules in dependency order.  (Except
in one-shot mode; see notes with hsc_HPT decl in GHC.Driver.Env).

It is possible (though hard) to get this error through user behaviour.
  * Suppose package P (modules P1, P2) depends on package Q (modules Q1,
    Q2, with Q2 importing Q1)
  * We compile both packages.
  * Now we edit package Q so that it somehow depends on P
  * Now recompile Q with --make (without recompiling P).
  * Then Q1 imports, say, P1, which in turn depends on Q2. So Q2
    is a home-package module which is not yet in the HPT!  Disaster.

This actually happened with P=base, Q=ghc-prim, via the AMP warnings.
See #8320.
-}

findAndReadIface
  :: Logger
  -> NameCache
  -> FinderCache
  -> Hooks
  -> UnitState
  -> HomeUnit
  -> DynFlags
  -> SDoc            -- ^ Reason for loading the iface (used for tracing)
  -> InstalledModule -- ^ The unique identifier of the on-disk module we're looking for
  -> Module          -- ^ The *actual* module we're looking for.  We use
                     -- this to check the consistency of the requirements of the
                     -- module we read out.
  -> IsBootInterface -- ^ Looking for .hi-boot or .hi file
  -> IO (MaybeErr SDoc (ModIface, FilePath))
findAndReadIface logger name_cache fc hooks unit_state home_unit dflags doc_str mod wanted_mod hi_boot_file = do
  let profile = targetProfile dflags

  trace_if logger (sep [hsep [text "Reading",
                           if hi_boot_file == IsBoot
                             then text "[boot]"
                             else Outputable.empty,
                           text "interface for",
                           ppr mod <> semi],
                     nest 4 (text "reason:" <+> doc_str)])

  -- Check for GHC.Prim, and return its static interface
  -- See Note [GHC.Prim] in primops.txt.pp.
  -- TODO: make this check a function
  if mod `installedModuleEq` gHC_PRIM
      then do
          let iface = case ghcPrimIfaceHook hooks of
                       Nothing -> ghcPrimIface
                       Just h  -> h
          return (Succeeded (iface, "<built in interface for GHC.Prim>"))
      else do
          let fopts = initFinderOpts dflags
          -- Look for the file
          mb_found <- liftIO (findExactModule fc fopts unit_state home_unit mod)
          case mb_found of
              InstalledFound loc mod -> do
                  -- Found file, so read it
                  let file_path = addBootSuffix_maybe hi_boot_file (ml_hi_file loc)
                  -- See Note [Home module load error]
                  if isHomeInstalledModule home_unit mod &&
                     not (isOneShot (ghcMode dflags))
                      then return (Failed (homeModError mod loc))
                      else do
                        r <- read_file logger name_cache unit_state dflags wanted_mod file_path
                        case r of
                          Failed _
                            -> return ()
                          Succeeded (iface,fp)
                            -> load_dynamic_too_maybe logger name_cache unit_state
                                                      dflags wanted_mod
                                                      hi_boot_file iface fp
                        return r
              err -> do
                  trace_if logger (text "...not found")
                  return $ Failed $ cannotFindInterface
                                      unit_state
                                      home_unit
                                      profile
                                      (Iface_Errors.mayShowLocations dflags)
                                      (moduleName mod)
                                      err

-- | Check if we need to try the dynamic interface for -dynamic-too
load_dynamic_too_maybe :: Logger -> NameCache -> UnitState -> DynFlags -> Module -> IsBootInterface -> ModIface -> FilePath -> IO ()
load_dynamic_too_maybe logger name_cache unit_state dflags wanted_mod is_boot iface file_path
  -- Indefinite interfaces are ALWAYS non-dynamic.
  | not (moduleIsDefinite (mi_module iface)) = return ()
  | otherwise = dynamicTooState dflags  >>= \case
      DT_Dont   -> return ()
      DT_Failed -> return ()
      DT_Dyn    -> load_dynamic_too logger name_cache unit_state dflags wanted_mod is_boot iface file_path
      DT_OK     -> load_dynamic_too logger name_cache unit_state (setDynamicNow dflags) wanted_mod is_boot iface file_path

load_dynamic_too :: Logger -> NameCache -> UnitState -> DynFlags -> Module -> IsBootInterface -> ModIface -> FilePath -> IO ()
load_dynamic_too logger name_cache unit_state dflags wanted_mod is_boot iface file_path = do
  let dynFilePath = addBootSuffix_maybe is_boot
                  $ replaceExtension file_path (hiSuf dflags)
  read_file logger name_cache unit_state dflags wanted_mod dynFilePath >>= \case
    Succeeded (dynIface, _)
     | mi_mod_hash (mi_final_exts iface) == mi_mod_hash (mi_final_exts dynIface)
     -> return ()
     | otherwise ->
        do trace_if logger (text "Dynamic hash doesn't match")
           setDynamicTooFailed dflags
    Failed err ->
        do trace_if logger (text "Failed to load dynamic interface file:" $$ err)
           setDynamicTooFailed dflags

read_file :: Logger -> NameCache -> UnitState -> DynFlags -> Module -> FilePath -> IO (MaybeErr SDoc (ModIface, FilePath))
read_file logger name_cache unit_state dflags wanted_mod file_path = do
  trace_if logger (text "readIFace" <+> text file_path)

  -- Figure out what is recorded in mi_module.  If this is
  -- a fully definite interface, it'll match exactly, but
  -- if it's indefinite, the inside will be uninstantiated!
  let wanted_mod' =
        case getModuleInstantiation wanted_mod of
            (_, Nothing) -> wanted_mod
            (_, Just indef_mod) ->
              instModuleToModule unit_state
                (uninstantiateInstantiatedModule indef_mod)
  read_result <- readIface dflags name_cache wanted_mod' file_path
  case read_result of
    Failed err -> return (Failed (badIfaceFile file_path err))
    Succeeded iface -> return (Succeeded (iface, file_path))
                -- Don't forget to fill in the package name...


-- | Write interface file
writeIface :: Logger -> Profile -> FilePath -> ModIface -> IO ()
writeIface logger profile hi_file_path new_iface
    = do createDirectoryIfMissing True (takeDirectory hi_file_path)
         let printer = TraceBinIFace (debugTraceMsg logger 3)
         writeBinIface profile printer hi_file_path new_iface

-- | @readIface@ tries just the one file.
--
-- Failed err    <=> file not found, or unreadable, or illegible
-- Succeeded iface <=> successfully found and parsed
readIface
  :: DynFlags
  -> NameCache
  -> Module
  -> FilePath
  -> IO (MaybeErr SDoc ModIface)
readIface dflags name_cache wanted_mod file_path = do
  let profile = targetProfile dflags
  res <- tryMost $ readBinIface profile name_cache CheckHiWay QuietBinIFace file_path
  case res of
    Right iface
        -- NB: This check is NOT just a sanity check, it is
        -- critical for correctness of recompilation checking
        -- (it lets us tell when -this-unit-id has changed.)
        | wanted_mod == actual_mod
                        -> return (Succeeded iface)
        | otherwise     -> return (Failed err)
        where
          actual_mod = mi_module iface
          err = hiModuleNameMismatchWarn wanted_mod actual_mod

    Left exn    -> return (Failed (text (showException exn)))

{-
*********************************************************
*                                                       *
        Wired-in interface for GHC.Prim
*                                                       *
*********************************************************
-}

-- See Note [GHC.Prim] in primops.txt.pp.
ghcPrimIface :: ModIface
ghcPrimIface
  = empty_iface {
        mi_exports  = ghcPrimExports,
        mi_decls    = [],
        mi_fixities = fixities,
        mi_final_exts = (mi_final_exts empty_iface){ mi_fix_fn = mkIfaceFixCache fixities },
        mi_decl_docs = ghcPrimDeclDocs -- See Note [GHC.Prim Docs]
        }
  where
    empty_iface = emptyFullModIface gHC_PRIM

    -- The fixity listed here for @`seq`@ should match
    -- those in primops.txt.pp (from which Haddock docs are generated).
    fixities = (getOccName seqId, Fixity NoSourceText 0 InfixR)
             : mapMaybe mkFixity allThePrimOps
    mkFixity op = (,) (primOpOcc op) <$> primOpFixity op

{-
*********************************************************
*                                                      *
\subsection{Statistics}
*                                                      *
*********************************************************
-}

ifaceStats :: ExternalPackageState -> SDoc
ifaceStats eps
  = hcat [text "Renamer stats: ", msg]
  where
    stats = eps_stats eps
    msg = vcat
        [int (n_ifaces_in stats) <+> text "interfaces read",
         hsep [ int (n_decls_out stats), text "type/class/variable imported, out of",
                int (n_decls_in stats), text "read"],
         hsep [ int (n_insts_out stats), text "instance decls imported, out of",
                int (n_insts_in stats), text "read"],
         hsep [ int (n_rules_out stats), text "rule decls imported, out of",
                int (n_rules_in stats), text "read"]
        ]

{-
************************************************************************
*                                                                      *
                Printing interfaces
*                                                                      *
************************************************************************

Note [Name qualification with --show-iface]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In order to disambiguate between identifiers from different modules, we qualify
all names that don't originate in the current module. In order to keep visual
noise as low as possible, we keep local names unqualified.

For some background on this choice see trac #15269.
-}

-- | Read binary interface, and print it out
showIface :: Logger -> DynFlags -> UnitState -> NameCache -> FilePath -> IO ()
showIface logger dflags unit_state name_cache filename = do
   let profile = targetProfile dflags
       printer = logMsg logger MCOutput noSrcSpan . withPprStyle defaultDumpStyle

   -- skip the hi way check; we don't want to worry about profiled vs.
   -- non-profiled interfaces, for example.
   iface <- readBinIface profile name_cache IgnoreHiWay (TraceBinIFace printer) filename

   let -- See Note [Name qualification with --show-iface]
       qualifyImportedNames mod _
           | mod == mi_module iface = NameUnqual
           | otherwise              = NameNotInScope1
       print_unqual = QueryQualify qualifyImportedNames
                                   neverQualifyModules
                                   neverQualifyPackages
   logMsg logger MCDump noSrcSpan
      $ withPprStyle (mkDumpStyle print_unqual)
      $ pprModIface unit_state iface

-- | Show a ModIface but don't display details; suitable for ModIfaces stored in
-- the EPT.
pprModIfaceSimple :: UnitState -> ModIface -> SDoc
pprModIfaceSimple unit_state iface =
    ppr (mi_module iface)
    $$ pprDeps unit_state (mi_deps iface)
    $$ nest 2 (vcat (map pprExport (mi_exports iface)))

-- | Show a ModIface
--
-- The UnitState is used to pretty-print units
pprModIface :: UnitState -> ModIface -> SDoc
pprModIface unit_state iface@ModIface{ mi_final_exts = exts }
 = vcat [ text "interface"
                <+> ppr (mi_module iface) <+> pp_hsc_src (mi_hsc_src iface)
                <+> (if mi_orphan exts then text "[orphan module]" else Outputable.empty)
                <+> (if mi_finsts exts then text "[family instance module]" else Outputable.empty)
                <+> (if mi_hpc iface then text "[hpc]" else Outputable.empty)
                <+> integer hiVersion
        , nest 2 (text "interface hash:" <+> ppr (mi_iface_hash exts))
        , nest 2 (text "ABI hash:" <+> ppr (mi_mod_hash exts))
        , nest 2 (text "export-list hash:" <+> ppr (mi_exp_hash exts))
        , nest 2 (text "orphan hash:" <+> ppr (mi_orphan_hash exts))
        , nest 2 (text "flag hash:" <+> ppr (mi_flag_hash exts))
        , nest 2 (text "opt_hash:" <+> ppr (mi_opt_hash exts))
        , nest 2 (text "hpc_hash:" <+> ppr (mi_hpc_hash exts))
        , nest 2 (text "plugin_hash:" <+> ppr (mi_plugin_hash exts))
        , nest 2 (text "src_hash:" <+> ppr (mi_src_hash iface))
        , nest 2 (text "sig of:" <+> ppr (mi_sig_of iface))
        , nest 2 (text "used TH splices:" <+> ppr (mi_used_th iface))
        , nest 2 (text "where")
        , text "exports:"
        , nest 2 (vcat (map pprExport (mi_exports iface)))
        , pprDeps unit_state (mi_deps iface)
        , vcat (map pprUsage (mi_usages iface))
        , vcat (map pprIfaceAnnotation (mi_anns iface))
        , pprFixities (mi_fixities iface)
        , vcat [ppr ver $$ nest 2 (ppr decl) | (ver,decl) <- mi_decls iface]
        , vcat (map ppr (mi_insts iface))
        , vcat (map ppr (mi_fam_insts iface))
        , vcat (map ppr (mi_rules iface))
        , ppr (mi_warns iface)
        , pprTrustInfo (mi_trust iface)
        , pprTrustPkg (mi_trust_pkg iface)
        , vcat (map ppr (mi_complete_matches iface))
        , text "module header:" $$ nest 2 (ppr (mi_doc_hdr iface))
        , text "declaration docs:" $$ nest 2 (ppr (mi_decl_docs iface))
        , text "arg docs:" $$ nest 2 (ppr (mi_arg_docs iface))
        , text "extensible fields:" $$ nest 2 (pprExtensibleFields (mi_ext_fields iface))
        ]
  where
    pp_hsc_src HsBootFile = text "[boot]"
    pp_hsc_src HsigFile = text "[hsig]"
    pp_hsc_src HsSrcFile = Outputable.empty

{-
When printing export lists, we print like this:
        Avail   f               f
        AvailTC C [C, x, y]     C(x,y)
        AvailTC C [x, y]        C!(x,y)         -- Exporting x, y but not C
-}

pprExport :: IfaceExport -> SDoc
pprExport (Avail n)      = ppr n
pprExport (AvailTC _ []) = Outputable.empty
pprExport avail@(AvailTC n _) =
    ppr n <> mark <> pp_export (availSubordinateGreNames avail)
  where
    mark | availExportsDecl avail = Outputable.empty
         | otherwise              = vbar

    pp_export []    = Outputable.empty
    pp_export names = braces (hsep (map ppr names))

pprUsage :: Usage -> SDoc
pprUsage usage@UsagePackageModule{}
  = pprUsageImport usage usg_mod
pprUsage usage@UsageHomeModule{}
  = pprUsageImport usage usg_mod_name $$
    nest 2 (
        maybe Outputable.empty (\v -> text "exports: " <> ppr v) (usg_exports usage) $$
        vcat [ ppr n <+> ppr v | (n,v) <- usg_entities usage ]
        )
pprUsage usage@UsageFile{}
  = hsep [text "addDependentFile",
          doubleQuotes (text (usg_file_path usage)),
          ppr (usg_file_hash usage)]
pprUsage usage@UsageMergedRequirement{}
  = hsep [text "merged", ppr (usg_mod usage), ppr (usg_mod_hash usage)]
pprUsage usage@UsageHomeModuleInterface{}
  = hsep [text "implementation", ppr (usg_mod_name usage), ppr (usg_iface_hash usage)]

pprUsageImport :: Outputable a => Usage -> (Usage -> a) -> SDoc
pprUsageImport usage usg_mod'
  = hsep [text "import", safe, ppr (usg_mod' usage),
                       ppr (usg_mod_hash usage)]
    where
        safe | usg_safe usage = text "safe"
             | otherwise      = text " -/ "

-- | Pretty-print unit dependencies
pprDeps :: UnitState -> Dependencies -> SDoc
pprDeps unit_state (Deps { dep_direct_mods = dmods
                         , dep_boot_mods = bmods
                         , dep_orphs = orphs
                         , dep_direct_pkgs = pkgs
                         , dep_trusted_pkgs = tps
                         , dep_finsts = finsts
                         })
  = pprWithUnitState unit_state $
    vcat [text "direct module dependencies:" <+> fsep (map ppr_mod dmods),
          text "boot module dependencies:" <+> fsep (map ppr bmods),
          text "direct package dependencies:" <+> fsep (map ppr_pkg pkgs),
          if null tps then empty else text "trusted package dependencies:" <+> fsep (map ppr_pkg pkgs),
          text "orphans:" <+> fsep (map ppr orphs),
          text "family instance modules:" <+> fsep (map ppr finsts)
        ]
  where
    ppr_mod (GWIB { gwib_mod = mod_name, gwib_isBoot = boot }) = ppr mod_name <+> ppr_boot boot
    ppr_pkg pkg  = ppr pkg
    ppr_boot IsBoot  = text "[boot]"
    ppr_boot NotBoot = Outputable.empty

pprFixities :: [(OccName, Fixity)] -> SDoc
pprFixities []    = Outputable.empty
pprFixities fixes = text "fixities" <+> pprWithCommas pprFix fixes
                  where
                    pprFix (occ,fix) = ppr fix <+> ppr occ

pprTrustInfo :: IfaceTrustInfo -> SDoc
pprTrustInfo trust = text "trusted:" <+> ppr trust

pprTrustPkg :: Bool -> SDoc
pprTrustPkg tpkg = text "require own pkg trusted:" <+> ppr tpkg

instance Outputable Warnings where
    ppr = pprWarns

pprWarns :: Warnings -> SDoc
pprWarns NoWarnings         = Outputable.empty
pprWarns (WarnAll txt)  = text "Warn all" <+> ppr txt
pprWarns (WarnSome prs) = text "Warnings"
                        <+> vcat (map pprWarning prs)
    where pprWarning (name, txt) = ppr name <+> ppr txt

pprIfaceAnnotation :: IfaceAnnotation -> SDoc
pprIfaceAnnotation (IfaceAnnotation { ifAnnotatedTarget = target, ifAnnotatedValue = serialized })
  = ppr target <+> text "annotated by" <+> ppr serialized

pprExtensibleFields :: ExtensibleFields -> SDoc
pprExtensibleFields (ExtensibleFields fs) = vcat . map pprField $ toList fs
  where
    pprField (name, (BinData size _data)) = text name <+> text "-" <+> ppr size <+> text "bytes"
