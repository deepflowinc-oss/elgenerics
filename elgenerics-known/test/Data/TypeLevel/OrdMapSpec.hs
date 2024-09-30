{-# LANGUAGE AllowAmbiguousTypes #-}
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
{-# OPTIONS_GHC -fplugin Data.TypeLevel.List.Solver #-}

module Data.TypeLevel.OrdMapSpec where

import Data.Proxy
import Data.TypeLevel.OrdMap
import Data.TypeLevel.OrdMapSpec.Cases
import Data.TypeLevel.OrdMapSpec.Failures
import GHC.TypeNats
import Helpers (expectInspectionFail, testInspection)
import Test.Tasty
import Test.Tasty.HUnit
import Type.Reflection

type TypeLabelledFields =
  FromList
    '[ String ::: 2
     , Int ::: 4
     , Maybe Bool ::: 3
     , () ::: 0
     , Ordering ::: 5
     ]

infixr 9 <:

type (<:) x xs = Insert (Label x) (Entry x) xs

type RawTypeFields =
  ( (Ordering ::: 5)
      <: (Maybe Bool ::: 3)
      <: (Int ::: 4)
      <: (String ::: 2)
      <: Singleton () 0
  )

test_foldMapOrdMapC :: TestTree
test_foldMapOrdMapC =
  testGroup
    "foldMapOrdMapC"
    [ testCase "TypeLabelledFields" $
        foldMapOrdMapC @(LabelC Typeable)
          @TypeLabelledFields
          ( \(Proxy :: Proxy ty) _ _ ->
              [show $ typeRep @ty]
          )
          @?= [ show (typeRep @())
              , show (typeRep @Int)
              , show (typeRep @Ordering)
              , show (typeRep @(Maybe Bool))
              , show (typeRep @String)
              ]
    , testCase "RawTypeFields" $
        foldMapOrdMapC @(LabelC Typeable)
          @RawTypeFields
          ( \(Proxy :: Proxy ty) _ _ ->
              [show $ typeRep @ty]
          )
          @?= [ show (typeRep @())
              , show (typeRep @Int)
              , show (typeRep @Ordering)
              , show (typeRep @(Maybe Bool))
              , show (typeRep @String)
              ]
    ]

test_foldMapOrdMap :: TestTree
test_foldMapOrdMap =
  testGroup
    "foldMapOrdMap"
    [ testCase "TypeLabelledFields" $
        foldMapOrdMap
          @TypeLabelledFields
          (\_ _ n -> [natVal n])
          @?= [0 .. (4 :: Natural)]
    , testCase "RawTypeFields" $
        foldMapOrdMap
          @RawTypeFields
          (\_ _ n -> [natVal n])
          @?= [0 .. (4 :: Natural)]
    ]

test_foldMapOrdMapC' :: TestTree
test_foldMapOrdMapC' =
  testGroup
    "foldMapOrdMapC'"
    [ testCase "TypeLabelledFields" $
        foldMapOrdMapC' @(LabelC Typeable)
          @TypeLabelledFields
          ( \(Proxy :: Proxy ty) _ _ ->
              [show $ typeRep @ty]
          )
          @?= [ show (typeRep @())
              , show (typeRep @Int)
              , show (typeRep @Ordering)
              , show (typeRep @(Maybe Bool))
              , show (typeRep @String)
              ]
    , testCase "RawTypeFields" $
        foldMapOrdMapC' @(LabelC Typeable)
          @RawTypeFields
          ( \(Proxy :: Proxy ty) _ _ ->
              [show $ typeRep @ty]
          )
          @?= [ show (typeRep @())
              , show (typeRep @Int)
              , show (typeRep @Ordering)
              , show (typeRep @(Maybe Bool))
              , show (typeRep @String)
              ]
    ]

test_foldMapOrdMap' :: TestTree
test_foldMapOrdMap' =
  testGroup
    "foldMapOrdMap'"
    [ testCase "TypeLabelledFields" $
        foldMapOrdMap'
          @TypeLabelledFields
          (\_ _ n -> [natVal n])
          @?= [0 .. (4 :: Natural)]
    , testCase "RawTypeFields" $
        foldMapOrdMap'
          @RawTypeFields
          (\_ _ n -> [natVal n])
          @?= [0 .. (4 :: Natural)]
    ]

test_FromAscList :: TestTree
test_FromAscList =
  testGroup
    "FromAscList"
    [ expectInspectionFail "should reject unsorted list" unsortedFromAscList
    ]

test_FromList :: TestTree
test_FromList =
  testGroup
    "FromList"
    [ testGroup
        "should generate valid Red-Black tree"
        [ testInspection "[20, 30, 40, 50, 10, 2, 0, 1]" test011
        , testInspection "[1,2,3,4,0]" test01
        , testInspection "Insert 2 [0,1]" test02
        , testInspection "Insert 2 [0]" test03
        , testInspection "[1, 0]" test04
        ]
    ]

test_ValidRBTree :: TestTree
test_ValidRBTree =
  testGroup
    "ValidRBTree"
    [ expectInspectionFail "should reject unsorted RBTree" unsortedValidRBTree
    , expectInspectionFail "should reject red-red RBTree" redRedInvalid
    ]
