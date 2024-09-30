{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Data.Product.Class (
  HasFactor (..),
  getFactor,
  setFactor,
  GHasFactor,
  withHasFactor,
  withIdFactor,
  withHasFactorL,
  factorLWith,
  getFactorWith,
  setFactorWith,
) where

import Control.Lens (Lens', ReifiedLens (..), coerced, lens, set, view)
import Data.Proxy
import Data.TypeLevel.Maybe
import Data.TypeLevel.Path
import GHC.TypeLits
import Unsafe.Coerce

getFactor' :: ProdPath c f -> f () -> c
getFactor' K (K1 a) = a
getFactor' (M p) (M1 a) = getFactor' p a
getFactor' (GoL p) (l :*: _) = getFactor' p l
getFactor' (GoR p) (_ :*: r) = getFactor' p r

setFactor' :: ProdPath c f -> c -> f () -> f ()
setFactor' K c (K1 _) = K1 c
setFactor' (M p) c (M1 f) = M1 $ setFactor' p c f
setFactor' (GoL p) c (l :*: r) = setFactor' p c l :*: r
setFactor' (GoR p) c (l :*: r) = l :*: setFactor' p c r

getFactorWith :: (Generic a) => ProdPath c (Rep a) -> a -> c
getFactorWith p = getFactor' p . from

setFactorWith :: (Generic a) => ProdPath c (Rep a) -> c -> a -> a
{-# INLINE setFactorWith #-}
setFactorWith p = \c -> to . setFactor' p c . from

factorLWith :: forall c a. (Generic a) => ProdPath c (Rep a) -> Lens' a c
factorLWith path =
  coerced . lens (getFactorWith path) (flip $ setFactorWith @a @c path)

type FactorPath ::
  forall c -> forall a -> ProdPath c (Rep a)
type family FactorPath c a :: ProdPath c (Rep a) where
  FactorPath c a =
    FromJust
      ( 'Text "A type `"
          ':<>: 'ShowType a
          ':<>: 'Text "' doesn't have a field of type `"
          ':<>: 'ShowType c
          ':<>: 'Text "'"
      )
      (PositionOf ProdOnly c a)

class HasFactor c a where
  factorL :: Lens' a c
  default factorL :: (GHasFactor c a) => Lens' a c
  factorL = factorLWith (pathVal $ Proxy @(FactorPath c a))

type GHasFactor c a =
  (Generic a, KnownPath ProdOnly c (Rep a) (FactorPath c a))

-- instance {-# OVERLAPPABLE #-}
--     (Generic a, KnownPath ProdOnly c (Rep a) (FactorPath c a))
--   => HasFactor c a

getFactor :: forall c a. (HasFactor c a) => a -> c
getFactor = view factorL

setFactor :: forall c a. (HasFactor c a) => c -> a -> a
setFactor = set factorL

newtype WrapHF a b r = WrapHF ((HasFactor a b) => r)

withHasFactor ::
  forall a b r.
  (a -> b) ->
  (b -> a -> a) ->
  ((HasFactor b a) => r) ->
  r
withHasFactor f g = withHasFactorL (lens f $ flip g)
{-# INLINE withHasFactor #-}

withHasFactorL :: forall b a r. Lens' a b -> ((HasFactor b a) => r) -> r
withHasFactorL l act =
  unsafeCoerce (WrapHF @b @a @r act) (Lens l)
{-# INLINE withHasFactorL #-}

withIdFactor :: forall a r. ((HasFactor a a) => r) -> r
withIdFactor act = unsafeCoerce (WrapHF @a @a @r act) (Lens @a @a @a @a id)
{-# INLINE withIdFactor #-}
