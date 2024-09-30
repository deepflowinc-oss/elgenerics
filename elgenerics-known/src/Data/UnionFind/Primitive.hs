{-# LANGUAGE DerivingStrategies #-}

{- | Generic Union-Find implementation, wrapping @union-find@ package around
   'PrimMonad' interface.
   If you need extra operation on representatives on 'union' you can use this module.
   If you only need really fast union-find and no operations on representatives
   needed, consider using "Data.UnionFind.Fast".
-}
module Data.UnionFind.Primitive (
  Point,
  fresh,
  repr,
  union,
  equivalent,
  redundant,
  descriptor,
  setDescriptor,
  modifyDescriptor,

  -- * Re-exports
  PrimMonad (..),
) where

import Control.Monad.Primitive
import Data.Function
import Data.UnionFind.ST qualified as UF

newtype Point m a = PPoint {unPoint :: UF.Point (PrimState m) a}
  deriving newtype (Eq)

fresh :: (PrimMonad m) => a -> m (Point m a)
fresh = fmap PPoint . stToPrim . UF.fresh

repr :: (PrimMonad m) => Point m a -> m (Point m a)
repr = fmap PPoint . stToPrim . UF.repr . unPoint

union :: (PrimMonad m) => Point m a -> Point m a -> m ()
union = fmap stToPrim <$> UF.union `on` unPoint

equivalent :: (PrimMonad m) => Point m a -> Point m a -> m Bool
equivalent = fmap stToPrim <$> UF.equivalent `on` unPoint

redundant :: (PrimMonad m) => Point m a -> m Bool
redundant = stToPrim . UF.redundant . unPoint

descriptor :: (PrimMonad m) => Point m a -> m a
descriptor = stToPrim . UF.descriptor . unPoint

setDescriptor :: (PrimMonad m) => Point m a -> a -> m ()
setDescriptor = fmap stToPrim . UF.setDescriptor . unPoint

modifyDescriptor :: (PrimMonad m) => Point m a -> (a -> a) -> m ()
modifyDescriptor = fmap stToPrim . UF.modifyDescriptor . unPoint
