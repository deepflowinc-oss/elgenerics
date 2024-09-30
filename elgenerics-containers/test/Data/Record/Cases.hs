{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.List.Overloaded #-}

module Data.Record.Cases where

import Data.Kind (Type)
import Data.Record (IsRecord)
import Data.Record qualified as Simple
import Data.Record.HigherKinded (
  FromAscList,
  HRecordable,
  IsHRecord,
  Recordable,
  (:::),
 )
import Data.Record.HigherKinded qualified as HK
import Data.Type.Equality (type (~~))
import GHC.Generics (Generic)
import GHC.TypeLits (Symbol)
import Test.QuickCheck (Arbitrary (..), genericShrink)

type AscFields1 = FromAscList '["a" ::: Int, "b" ::: Bool, "c" ::: ()]

ascSimpleRecord1 :: Simple.Record AscFields1
ascSimpleRecord1 =
  Simple.emptyRec
    Simple.&+ #a
    Simple.:= 12
    Simple.&+ #b
    Simple.:= False
    Simple.&+ #c
    Simple.:= ()

mkAscSimpleRecord1 :: Int -> Bool -> () -> Simple.Record AscFields1
mkAscSimpleRecord1 a b c =
  Simple.emptyRec
    Simple.&+ #a
    Simple.:= a
    Simple.&+ #b
    Simple.:= b
    Simple.&+ #c
    Simple.:= c

newtype Foo a = Foo {unFoo :: Simple.Record '["a" ::: Int, "b" ::: a, "c" ::: ()]}
  deriving (Generic, Show, Eq)
  deriving anyclass (IsRecord)

deriving anyclass instance IsHRecord HK.STagged (Foo a)

data Bar c = Bar {a :: Int, b :: Bool, c :: c}
  deriving (Generic, Show, Eq)

deriving anyclass instance (Recordable (Bar c)) => IsRecord (Bar c)

data Buz a = Buz {buzX :: Maybe Int, buzY :: Maybe Bool, buzZ :: a}
  deriving (Generic, Show, Eq, Ord)

deriving anyclass instance (Recordable (Buz a)) => IsRecord (Buz a)

deriving anyclass instance
  IsHRecord (HK.OnEntry Maybe :: Symbol -> Type -> Type) (Buz (Maybe a))

instance (Arbitrary a) => Arbitrary (Buz a) where
  arbitrary = Buz <$> arbitrary <*> arbitrary <*> arbitrary
  shrink = genericShrink

data Buz0 = Buz0 {ddd :: Maybe Int, ggg :: Maybe Bool}
  deriving (Generic, Show, Eq, Ord)
  deriving anyclass (IsRecord)

deriving anyclass instance
  IsHRecord (HK.OnEntry Maybe :: Symbol -> Type -> Type) Buz0

instance Arbitrary Buz0 where
  arbitrary = Buz0 <$> arbitrary <*> arbitrary
  shrink = genericShrink

data MyHKD h = MyHKD {hInt :: h Int, hBool :: h Bool}
  deriving (Generic)

deriving instance (Recordable (MyHKD h)) => IsRecord (MyHKD h)

deriving stock instance (Show (h Int), Show (h Bool)) => Show (MyHKD h)

deriving anyclass instance
  ( HRecordable (HK.OnEntry h :: Symbol -> Type -> Type) (MyHKD h)
  , HK.OnEntry h ~~ (h' :: Symbol -> Type -> Type)
  ) =>
  IsHRecord h' (MyHKD h)
