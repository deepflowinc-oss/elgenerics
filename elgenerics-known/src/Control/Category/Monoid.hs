{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}

-- | Monoid instances made out of @'Arrows'@
module Control.Category.Monoid (EndoC (..), EndoM (..)) where

import Control.Arrow
import Control.Category as Cat
import Data.Coerce

newtype EndoC p a = EndoC {appEndoA :: p a a}

instance (Category p) => Semigroup (EndoC p a) where
  (<>) = coerce $ (Cat..) @p @a @a @a

instance (Category p) => Monoid (EndoC p a) where
  mempty = coerce $ Cat.id @p @a

newtype EndoM m a = EndoM {appEndoM :: a -> m a}
  deriving
    (Semigroup, Monoid)
    via EndoC (Kleisli m) a
