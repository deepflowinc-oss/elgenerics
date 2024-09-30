{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O -dsuppress-all -dno-suppress-type-signatures #-}

module Data.TypeLevel.NatSpec where

import Data.Proxy (Proxy)
import Data.TypeLevel.Nat.Definitions
import Numeric.Natural (Natural)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.ExpectedFailure (ignoreTestBecause)
import Test.Tasty.Inspection

branchTNat0 :: Proxy 0 -> Natural
branchTNat0 = branchTNat

proxy0 :: Proxy 0 -> Natural
proxy0 _ = 0

branchTNat1 :: Proxy 1 -> Natural
branchTNat1 = branchTNat

proxy1 :: Proxy 1 -> Natural
proxy1 _ = 1

test_tnat :: TestTree
test_tnat =
  ignoreTestBecause "These tests fails with FAST build, even with module option -O" $
    testGroup
      "tnat erases concrete"
      [ $(inspectTest $ 'branchTNat0 ==- 'proxy0)
      , $(inspectTest $ 'branchTNat1 ==- 'proxy1)
      ]
