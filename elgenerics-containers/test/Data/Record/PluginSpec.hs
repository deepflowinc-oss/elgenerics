{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin Data.Record.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Data.Record.Plugin:MyRecord #-}

module Data.Record.PluginSpec where

import Control.Lens ((^.))
import Data.Record (Record, fieldL, (:::))
import Data.TypeLevel.OrdMap (FromAscList)
import Test.Tasty (TestTree)
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.QuickCheck (conjoin, testProperty, (===))

type Record1 = Record (FromAscList '["a" ::: Int, "b" ::: Bool, "c" ::: ()])

record :: Record1
record = MyRecord {a = 42 :: Int, b = False, c = ()}

test_RecordPlugin_Cons :: TestTree
test_RecordPlugin_Cons =
  testCase "Constructor gives an expected result" do
    record ^. fieldL #a @?= (42 :: Int)
    record ^. fieldL #b @?= False
    record ^. fieldL #c @?= ()

test_Record_Random :: TestTree
test_Record_Random = testProperty "Randomly generated field cons" $
  \int p unit ->
    let r :: Record1
        r = MyRecord {a = int :: Int, b = p :: Bool, c = unit :: ()}
     in conjoin
          [ r ^. fieldL #a === int
          , r ^. fieldL #b === p
          , r ^. fieldL #c === unit
          ]
