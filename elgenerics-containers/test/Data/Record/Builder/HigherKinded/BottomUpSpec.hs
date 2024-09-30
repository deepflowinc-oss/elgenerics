{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Wno-orphans -Wno-partial-type-signatures #-}

module Data.Record.Builder.HigherKinded.BottomUpSpec where

import Control.Arrow (
  Arrow (second),
  first,
 )
import Data.DList qualified as DL
import Data.Function (on)
import Data.Functor.Const (Const (Const))
import Data.Kind (Type)
import Data.List (nub, nubBy, sortOn)
import Data.Proxy (Proxy)
import Data.Record.Builder.HigherKinded.BottomUp (
  RecordBuilder,
  build,
 )
import Data.Record.Builder.HigherKinded.BottomUp qualified as Bup
import Data.Record.Cases
import Data.Record.HigherKinded (
  Field,
  OnEntry (OnEntry),
  field,
  foldMapRec,
  fromHRecord,
  fromRecord,
  (:=) (..),
 )
import Data.Tagged (Tagged (Tagged))
import Data.TypeLevel.Known (
  HasSing (promote),
  Known,
  SList (..),
  SNat,
  SomeSing (MkSomeSing),
  sKnownVal',
  withKnown',
  withKnownNat',
 )
import Data.TypeLevel.Nat (Nat, natVal)
import Data.TypeLevel.OrdMap (
  SField ((:%::)),
  SortableLabels,
  sSortPermutation,
 )
import Test.QuickCheck (
  NonNegative (..),
  PrintableString (..),
  (===),
 )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (
  tabulate,
  testProperty,
 )
import Type.Reflection (Typeable, typeRep)

type H = OnEntry (Const (Integer, String))

data SomeRecordBuilder where
  MkRecBuilder ::
    (SortableLabels ps, Known ps, Typeable ps) =>
    RecordBuilder H (ps :: [Field Nat Type]) ->
    SomeRecordBuilder

test_Buz0 :: TestTree
test_Buz0 =
  testGroup
    "Builds fixed record into native record properly"
    [ testProperty "Simple" \buz0@Buz0 {..} ->
        fromRecord
          ( Bup.build $
              Bup.empty
                Bup.&+ #ddd
                := Tagged ddd
                Bup.&+ #ggg
                := Tagged ggg
          )
          === buz0
    , testProperty "Higher-Kinded" \buz0@Buz0 {..} ->
        fromHRecord @(OnEntry Maybe) @Buz0
          ( Bup.build $
              Bup.empty
                Bup.&+ #ddd
                := OnEntry ddd
                Bup.&+ #ggg
                := OnEntry ggg
          )
          === buz0
    ]

test_builder :: TestTree
test_builder = testProperty "Builds random records properly" $
  \(as0 :: [(NonNegative Integer, PrintableString)]) ->
    let as = map (first getNonNegative) as0
        us = nubBy ((==) `on` fst) as
        sorted = map (second getPrintableString) $ sortOn fst us
     in case promote @[Nat] $ map (fromIntegral . fst) us of
          MkSomeSing (slist :: SList ps) ->
            case toRecordBuilder slist $ map (getPrintableString . snd) us of
              MkRecBuilder builder ->
                tabulate "# of Elements" [show $ length us]
                  $ tabulate
                    "# of distinct associated values"
                    [show $ length $ nub $ map snd us]
                  $ let lst =
                          foldMapRec
                            ( \(_ :: Proxy k) (_ :: Proxy l) _ (OnEntry (Const s)) ->
                                DL.singleton s
                            )
                            $ build builder
                     in DL.toList lst === sorted

toRecordBuilder :: SList (a :: [Nat]) -> [String] -> SomeRecordBuilder
toRecordBuilder SNil _ = MkRecBuilder Bup.empty
toRecordBuilder (:%) {} [] = error "toRecordBuilder: Could not happen!"
toRecordBuilder ((a :: SNat n) :% as) (x : xs) =
  withKnownNat' a $
    case toRecordBuilder as xs of
      MkRecBuilder (b0 :: RecordBuilder H ps) ->
        withKnown' (sSortPermutation $ (a :%:: typeRep @Type) :% sKnownVal' @ps) $
          MkRecBuilder $
            b0
              Bup.&+ field @n
              := OnEntry (Const (fromIntegral $ natVal a, x) :: Const (Integer, String) Type)
