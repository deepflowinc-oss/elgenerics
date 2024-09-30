{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Data.Constraint.Deferrable.SolverSpec where

import Data.Constraint.Deferrable.SolverSpec.Cases
import Data.Constraint.Deferrable.SolverSpec.Undeferreds
import Data.Proxy (Proxy (Proxy))
import Helpers
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

test_DeferrableSolver :: TestTree
test_DeferrableSolver =
  testGroup
    "DeferrableSolver"
    [ testCase "Cannot defer unavailable constraint (no instance)" $
        shouldThrowTypeError deferInaccessible
    , testCase "Cannot defer constraint" $
        shouldThrowTypeError undeferrableOk
    , testCase "Can defer constraint with specific overlapping instance" $
        shouldNotThrowTypeError deferrableOk
    , testCase "Can defer concrete (KnownNat 42)" $
        theUnit @?= Right ()
    , testCase "Can choose available dictionary, KnownNat n, polymorphically" $
        deferKnownNatN (Proxy @2) @?= Right 2
    , testCase "Can defer higher-order constraints correctly: fail for absent" $
        deferDummy @5 (knn (Proxy @Dummy) (Proxy @5))
          @?= Left "No dictionary"
    , testCase "Can defer higher-order constraints correctly: success if present" $
        deferDummy @1 (knn (Proxy @Dummy) (Proxy @1))
          @?= Right 1
    ]
