{-# LANGUAGE DataKinds #-}

module Data.TypeLevel.List.Properties where

import Data.TypeLevel.Function

class PreservesLength p

class
  MonotoneApply
    (p :: a ~> b)
    (cmp1 :: a ~> a ~> Ordering)
    (cmp2 :: b ~> b ~> Ordering)

class
  Monotone
    (p :: a -> b)
    (cmp1 :: a ~> a ~> Ordering)
    (cmp2 :: b ~> b ~> Ordering)

instance MonotoneApply Id1 c c

instance PreservesLength Id1

instance (Monotone f c d) => MonotoneApply (Con f) c d

instance (PreservesLength f) => PreservesLength (Con f)
