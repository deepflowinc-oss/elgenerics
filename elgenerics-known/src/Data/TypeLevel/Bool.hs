{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.TypeLevel.Bool (
  type (&&),
  (%&&),
  type (||),
  (%||),
  type Not,
  sNot,
  type CmpBool,
  sCmpBool,
) where

import Data.TypeLevel.Known

type family (&&) (a :: Bool) (b :: Bool) :: Bool where
  'True && b = b
  'False && _ = 'False

infixr 3 &&, %&&

(%&&) :: SBool a -> SBool b -> SBool (a && b)
STrue %&& a = a
SFalse %&& _ = SFalse

type family (||) (a :: Bool) (b :: Bool) :: Bool where
  'True || _ = 'True
  'False || b = b

infixr 2 ||, %||

(%||) :: SBool a -> SBool b -> SBool (a || b)
STrue %|| _ = STrue
SFalse %|| a = a

type family Not (a :: Bool) :: Bool where
  Not 'True = 'False
  Not 'False = 'True

sNot :: SBool a -> SBool (Not a)
sNot STrue = SFalse
sNot SFalse = STrue

type family CmpBool (l :: Bool) (r :: Bool) :: Ordering where
  CmpBool 'True 'True = 'EQ
  CmpBool 'False 'False = 'EQ
  CmpBool 'True 'False = 'GT
  CmpBool 'False 'True = 'LT

sCmpBool :: SBool l -> SBool r -> SOrdering (CmpBool l r)
sCmpBool SFalse SFalse = SEQ
sCmpBool SFalse STrue = SLT
sCmpBool STrue STrue = SEQ
sCmpBool STrue SFalse = SGT
