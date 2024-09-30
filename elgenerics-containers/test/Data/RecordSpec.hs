{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.RecordSpec where

import Data.Record (IsRecord (fromRecord), toRecord)
import Data.Record.Cases
import Data.Record.HigherKinded qualified as HK
import Test.Tasty
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.QuickCheck (testProperty, (.&&.), (===))

test_IsRecord_IsHRecord_newtype :: TestTree
test_IsRecord_IsHRecord_newtype =
  testCase "IsRecord/IsHRecord works properly for newtyped simple record" do
    let fromRecorded = fromRecord ascSimpleRecord1
        fromHReced = HK.fromHRecord ascSimpleRecord1
        directFoo = Foo @Bool ascSimpleRecord1
    fromRecorded @?= directFoo
    fromRecorded @?= fromHReced

test_IsRecord_IsHRecord_newtype_randomised :: TestTree
test_IsRecord_IsHRecord_newtype_randomised =
  testProperty
    "IsRecord/IsHRecord works properly for newtyped simple record (radom)"
    $ \x y z ->
      let fromRecorded = fromRecord $ mkAscSimpleRecord1 x y z
          fromHReced = HK.fromHRecord $ mkAscSimpleRecord1 x y z
          directFoo = Foo @Bool $ mkAscSimpleRecord1 x y z
       in fromRecorded === directFoo
            .&&. fromRecorded === fromHReced

test_nativeRecords :: TestTree
test_nativeRecords = testProperty
  "Conversion b/w native records"
  \x y z ->
    let ext = mkAscSimpleRecord1 x y z
        bar = Bar x y z
     in ext === toRecord bar .&&. fromRecord ext === bar
