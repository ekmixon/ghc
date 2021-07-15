{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
module GHC.Data.DependentMap where

import GHC.Prelude
import qualified Data.Map as M
import Unsafe.Coerce (unsafeCoerce)

newtype DependentMap k f = DependentMap (M.Map (AnyKey k) (AnyKey f))

insertDepMap :: GOrd k => k a -> f a -> DependentMap k f -> DependentMap k f
insertDepMap req resp (DependentMap rc)
  = DependentMap (M.insert (AnyKey req) (AnyKey resp) rc)

lookupDepMap :: forall k f a. GOrd k => k a -> DependentMap k f -> Maybe (f a)
lookupDepMap req (DependentMap rc) = coerceResult <$> M.lookup (AnyKey req) rc
  where
    coerceResult :: AnyKey f -> f a
    coerceResult (AnyKey a) = unsafeCoerce a

emptyDepMap :: DependentMap k f
emptyDepMap = DependentMap M.empty


-- A continuation is applied to each element to avoid exposing AnyKey
elemsDepMap :: (forall a . f a -> b) -> DependentMap k f -> [b]
elemsDepMap f (DependentMap rc) =
  map (\(AnyKey v) -> f v) (M.elems rc)

foldDepMap :: forall b k f . (forall a . b -> k a -> f a -> b) -> b -> DependentMap k f -> b
foldDepMap f i (DependentMap rc) = M.foldlWithKey (\b (AnyKey k) (AnyKey v) -> f b k (unsafeCoerce v)) i rc

data AnyKey f = forall a . AnyKey !(f a)

instance GOrd f => Eq (AnyKey f) where
  (AnyKey r1) == (AnyKey r2) = geq r1 r2

instance GOrd f => Ord (AnyKey f) where
  (AnyKey r1) `compare` (AnyKey r2) = gcompare r1 r2

data AnyVal = forall a . AnyVal !a


class GEq f => GOrd f where
    gcompare :: f a -> f b -> Ordering

class GEq f where
    geq :: f a -> f b -> Bool

