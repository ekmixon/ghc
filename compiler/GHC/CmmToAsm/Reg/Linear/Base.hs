{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
-- | Put common type definitions here to break recursive module dependencies.

module GHC.CmmToAsm.Reg.Linear.Base (
        BlockAssignment,

        Loc(..),
        regsOfLoc,

        -- for stats
        SpillReason(..),
        RegAllocStats(..),

        -- the allocator monad
        RA_State(..),

        RegLocMap(..), addToRLM, addToRLM_Directly, addToRLMUnsafe, addToRLMUnsafe_Directly, delFromRLM, delFromRLM_Directly,
        delFromRLMLoc, elemRLM, lookupRLM,
        filterRLM_Directly, lookupRLM_Directly, nonDetRLMToList, nonDetEqRLM,
        emptyRegLocMap, nonDetStrictFoldRLM_DirectlyM,
        delListFromRLM_Directly, delListFromRLM,
        isInReg, isInRegOrBoth
)

where

import GHC.Prelude

import Control.Applicative
import Data.Bifunctor
import qualified Data.Semigroup as Semi

import GHC.CmmToAsm.Reg.Linear.StackMap
import GHC.CmmToAsm.Reg.Liveness
import GHC.CmmToAsm.Config
import GHC.Platform.Reg

import GHC.Utils.Outputable
import GHC.Utils.Panic.Plain
import GHC.Types.Unique
import GHC.Types.Unique.FM
import GHC.Types.Unique.Supply
import GHC.Cmm.BlockId

data ReadingOrWriting = Reading | Writing deriving (Eq,Ord)

-- | Used to store the register assignment on entry to a basic block.
--      We use this to handle join points, where multiple branch instructions
--      target a particular label. We have to insert fixup code to make
--      the register assignments from the different sources match up.
--
type BlockAssignment freeRegs
        = BlockMap (freeRegs, RegLocMap)


-- | Where a vreg is currently stored
--      A temporary can be marked as living in both a register and memory
--      (InBoth), for example if it was recently loaded from a spill location.
--      This makes it cheap to spill (no save instruction required), but we
--      have to be careful to turn this into InReg if the value in the
--      register is changed.

--      This is also useful when a temporary is about to be clobbered.  We
--      save it in a spill location, but mark it as InBoth because the current
--      instruction might still want to read it.
--
data Loc
        -- | vreg is in a register
        = InReg   !RealReg

        -- | vreg is held in a stack slot
        | InMem   {-# UNPACK #-}  !StackSlot


        -- | vreg is held in both a register and a stack slot
        | InBoth   !RealReg
                   {-# UNPACK #-} !StackSlot
        deriving (Eq, Show, Ord)

instance Outputable Loc where
        ppr l = text (show l)

-- | Get the reg numbers stored in this Loc.
regsOfLoc :: Loc -> [RealReg]
regsOfLoc (InReg r)    = [r]
regsOfLoc (InBoth r _) = [r]
regsOfLoc (InMem _)    = []

data RegLocMap
        = RegLocMap {
                lm_inReg :: !(UniqFM VirtualReg Loc),
                lm_inMem :: !(UniqFM VirtualReg Loc),
                lm_inBoth :: !(UniqFM VirtualReg Loc)
                }

instance Semigroup RegLocMap where
        (<>)    (RegLocMap inReg1 inMem1 inBoth1)
                (RegLocMap inReg2 inMem2 inBoth2)
                =
                RegLocMap (inReg1 Semi.<> inReg2) (inMem1 Semi.<> inMem2) (inBoth1 Semi.<> inBoth2)

instance Monoid RegLocMap where
        mempty = RegLocMap mempty mempty mempty

instance Outputable RegLocMap where
        ppr (RegLocMap inReg inMem inBoth) =
                text "RegLocMap" <> parens (hcat [text "reg:" <> ppr inReg
                                                , text "mem:" <> ppr inMem
                                                , text "both:" <> ppr inBoth])
{-# SPECIALIZE elemRLM :: VirtualReg -> RegLocMap -> Bool #-}
{-# SPECIALIZE elemRLM :: Reg -> RegLocMap -> Bool #-}
elemRLM :: (IsReg reg) => reg -> RegLocMap -> Bool
elemRLM reg (RegLocMap inReg inMem inBoth) =
        assert(False) $
        elemUFM_Directly (getUnique reg) inReg ||
        elemUFM_Directly (getUnique reg) inMem ||
        elemUFM_Directly (getUnique reg) inBoth

{-# INLINE lookupRLM_Directly #-}
lookupRLM_Directly :: RegLocMap -> Unique -> Maybe Loc
lookupRLM_Directly (RegLocMap inReg inMem inBoth) unique =
        (lookupUFM_Directly inReg unique) <|>
        (lookupUFM_Directly inMem unique ) <|>
        (lookupUFM_Directly inBoth unique)

{-# SPECIALIZE lookupRLM :: RegLocMap -> Reg -> Maybe Loc #-}
{-# SPECIALIZE lookupRLM :: RegLocMap -> VirtualReg -> Maybe Loc #-}
{-# INLINE lookupRLM #-}
lookupRLM :: IsReg reg => RegLocMap -> reg -> Maybe Loc
lookupRLM assig@(RegLocMap inReg inMem inBoth) vreg =
        let !ureg = getUnique vreg in
        lookupRLM_Directly assig ureg

{-# INLINE delFromRLMLoc #-} -- Inlining allows all but one alternatives to become dead code.
                             -- since we pretty much only use this when we statically know what
                             -- the location is.
delFromRLMLoc :: Uniquable reg => RegLocMap -> reg -> Loc -> RegLocMap
delFromRLMLoc (RegLocMap inReg inMem inBoth) reg loc =
        let !ureg = getUnique reg
        in
        case loc of
                InReg {} ->
                        RegLocMap
                                (delFromUFM_Directly inReg ureg)
                                inMem
                                inBoth
                InMem {} ->
                        RegLocMap
                                inReg
                                (delFromUFM_Directly inMem ureg)
                                inBoth
                InBoth {} ->
                        RegLocMap
                                inReg
                                inMem
                                (delFromUFM_Directly inBoth ureg)


{-# SPECIALIZE delFromRLM :: RegLocMap -> VirtualReg -> RegLocMap #-}
{-# SPECIALIZE delFromRLM :: RegLocMap -> Reg -> RegLocMap #-}
delFromRLM :: IsReg reg => RegLocMap -> reg -> RegLocMap
delFromRLM (RegLocMap inReg inMem inBoth) reg =
        let !ureg = getUnique reg
        in
        RegLocMap
                (delFromUFM_Directly inReg ureg)
                (delFromUFM_Directly inMem ureg)
                (delFromUFM_Directly inBoth ureg)

delFromRLM_Directly :: RegLocMap -> Unique -> RegLocMap
delFromRLM_Directly (RegLocMap inReg inMem inBoth) ureg =
        RegLocMap
                (delFromUFM_Directly inReg ureg)
                (delFromUFM_Directly inMem ureg)
                (delFromUFM_Directly inBoth ureg)

{-# INLINE isInReg #-}
isInReg :: (IsReg reg) => reg -> RegLocMap -> Bool
isInReg reg (RegLocMap inReg _inMem _inBoth) =
        elemUFM_Directly (getUnique reg) inReg

{-# INLINE isInRegOrBoth #-}
isInRegOrBoth :: (IsReg reg) => reg -> RegLocMap -> Bool
isInRegOrBoth reg (RegLocMap inReg _inMem inBoth) =
        elemUFM_Directly (getUnique reg) inReg ||
        elemUFM_Directly (getUnique reg) inBoth


emptyRegLocMap :: RegLocMap
emptyRegLocMap = RegLocMap mempty mempty mempty

-- Values allowed to represent a register
class Uniquable r => IsReg r where

instance IsReg Reg
instance IsReg VirtualReg


-- | Not great for performance.
nonDetRLMToList (RegLocMap inReg inMem inBoth) =
        (nonDetUFMToList inReg) ++
        (nonDetUFMToList inMem) ++
        (nonDetUFMToList inBoth)

filterRLM_Directly :: (Unique -> Loc -> Bool) -> RegLocMap -> RegLocMap
filterRLM_Directly pred (RegLocMap inReg inMem inBoth) =
        RegLocMap
                (filterUFM_Directly pred inReg)
                (filterUFM_Directly pred inMem)
                (filterUFM_Directly pred inBoth)

nonDetEqRLM :: RegLocMap -> RegLocMap -> Bool
nonDetEqRLM (RegLocMap inReg1 inMem1 inBoth1) (RegLocMap inReg2 inMem2 inBoth2) =
        inReg1 `eqUFM` inReg2 &&
        inMem1 `eqUFM` inMem2 &&
        inBoth1 `eqUFM` inBoth2
        where eqUFM m1 m2 = m1 `nonDetCompareUFM` m2 == EQ


-- Add is slightly tricky. For UFM add replaces the current value.
-- Here it only does if the location is of the same type.
-- Removing from the other maps on insert seems expensive
-- but not doing so breaks compatiblity.

-- For now we assume that generally entries added are either the same type already
-- or they must be removed before adding the new one

addToRLM_Directly :: RegLocMap -> Unique -> Loc -> RegLocMap
addToRLM_Directly assig@(RegLocMap inReg inMem inBoth) ureg loc  =
        case loc of
            InReg {} ->
                RegLocMap
                        (addToUFM_Directly inReg ureg loc)
                        (delFromUFM_Directly inMem ureg)
                        (delFromUFM_Directly inBoth ureg)
            InMem {} ->
                RegLocMap
                        (delFromUFM_Directly inReg ureg)
                        (addToUFM_Directly inMem ureg loc)
                        (delFromUFM_Directly inBoth ureg)
            InBoth {} ->
                RegLocMap
                        (delFromUFM_Directly inReg ureg)
                        (delFromUFM_Directly inMem ureg)
                        (addToUFM_Directly inBoth ureg loc)

{-# INLINE addToRLM #-} -- Force specialization on the register type
addToRLM :: (IsReg vreg) => RegLocMap -> vreg -> Loc -> RegLocMap
addToRLM assig reg loc  =
        let !vreg = getUnique reg
        in addToRLM_Directly assig vreg loc

addToRLMUnsafe_Directly :: RegLocMap -> Unique -> Loc -> RegLocMap
addToRLMUnsafe_Directly assig@(RegLocMap inReg inMem inBoth) ureg loc  =
        case loc of
            InReg r ->
                assig { lm_inReg = addToUFM_Directly inReg ureg loc  }
            InMem m ->
                assig { lm_inMem = addToUFM_Directly inMem ureg loc  }
            InBoth {} ->
                assig { lm_inBoth = addToUFM_Directly inBoth ureg loc }

addToRLMUnsafe :: (IsReg vreg) => RegLocMap -> vreg -> Loc -> RegLocMap
addToRLMUnsafe assig reg loc  =
        let !vreg = getUnique reg
        in addToRLMUnsafe_Directly assig vreg loc

nonDetStrictFoldRLM_DirectlyM :: forall b m. (Monad m) => (Unique -> b -> Loc -> m b) -> b -> RegLocMap -> m b
nonDetStrictFoldRLM_DirectlyM f r (RegLocMap inReg inMem inBoth) = do
        let f' = f
        -- let f' :: Locable loc => Unique -> b -> loc -> m b
        --     f' u r l =  let loc = (toLoc l) :: Loc
        --                 in f u r loc
        r' <- nonDetStrictFoldUFM_DirectlyM f' r inReg
        r'' <- nonDetStrictFoldUFM_DirectlyM f' r' inMem
        r''' <- nonDetStrictFoldUFM_DirectlyM f' r'' inBoth
        return r'''


delListFromRLM_Directly :: RegLocMap -> [Unique] -> RegLocMap
delListFromRLM_Directly (RegLocMap inReg inMem inBoth) del =
        RegLocMap
                (delListFromUFM_Directly inReg del)
                (delListFromUFM_Directly inMem del)
                (delListFromUFM_Directly inBoth del)

delListFromRLM :: IsReg reg => RegLocMap -> [reg] -> RegLocMap
delListFromRLM (RegLocMap inReg inMem inBoth) del =
        RegLocMap
                (foldl' (\b e -> delFromUFM_Directly b (getUnique e)) inReg del)
                (foldl' (\b e -> delFromUFM_Directly b (getUnique e)) inMem del)
                (foldl' (\b e -> delFromUFM_Directly b (getUnique e)) inBoth del)
                -- (delListFromUFM inMem del)
                -- (delListFromUFM inBoth del)


-- | Reasons why instructions might be inserted by the spiller.
--      Used when generating stats for -ddrop-asm-stats.
--
data SpillReason
        -- | vreg was spilled to a slot so we could use its
        --      current hreg for another vreg
        = SpillAlloc    !Unique

        -- | vreg was moved because its hreg was clobbered
        | SpillClobber  !Unique

        -- | vreg was loaded from a spill slot
        | SpillLoad     !Unique

        -- | reg-reg move inserted during join to targets
        | SpillJoinRR   !Unique

        -- | reg-mem move inserted during join to targets
        | SpillJoinRM   !Unique


-- | Used to carry interesting stats out of the register allocator.
data RegAllocStats
        = RegAllocStats
        { ra_spillInstrs        :: UniqFM Unique [Int] -- Keys are the uniques of regs
                                                       -- and taken from SpillReason
                                                       -- See Note [UniqFM and the register allocator]
        , ra_fixupList     :: [(BlockId,BlockId,BlockId)]
        -- ^ (from,fixup,to) : We inserted fixup code between from and to
        }


-- | The register allocator state
data RA_State freeRegs
        = RA_State

        {
        -- | the current mapping from basic blocks to
        --      the register assignments at the beginning of that block.
          ra_blockassig :: BlockAssignment freeRegs

        -- | free machine registers
        , ra_freeregs   :: !freeRegs

        -- | assignment of temps to locations
        , ra_assig      :: RegLocMap

        -- | current stack delta
        , ra_delta      :: Int

        -- | free stack slots for spilling
        , ra_stack      :: StackMap

        -- | unique supply for generating names for join point fixup blocks.
        , ra_us         :: UniqSupply

        -- | Record why things were spilled, for -ddrop-asm-stats.
        --      Just keep a list here instead of a map of regs -> reasons.
        --      We don't want to slow down the allocator if we're not going to emit the stats.
        , ra_spills     :: [SpillReason]

        -- | Native code generator configuration
        , ra_config     :: !NCGConfig

        -- | (from,fixup,to) : We inserted fixup code between from and to
        , ra_fixups     :: [(BlockId,BlockId,BlockId)]

        }


