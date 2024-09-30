{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module Data.TypeLevel.KnownSpec where

import Data.TypeLevel.Known
import GHC.TypeLits (Nat)
import Test.Tasty
import Test.Tasty.HUnit

maybePureUnit :: (Applicative m) => SMaybe may -> m ()
maybePureUnit arg = $(sCases ''Maybe [|arg|] [|pure ()|])

test_sCases_Maybe :: TestTree
test_sCases_Maybe = testCase "sCases on Maybe works properly" $ do
  let sNot = SNothing :: SMaybe ('Nothing :: Maybe Nat)
  maybePureUnit sNot
  maybePureUnit $ SJust (sKnownVal' @4)

test_sCases_Bool :: TestTree
test_sCases_Bool = testCase "sCases on Bool works properly" $ do
  boolPureUnit SFalse
  boolPureUnit STrue

test_sCases_Bool_safe_depends :: TestTree
test_sCases_Bool_safe_depends =
  testCase "sCases on Bool, depending on the value itself only in expression, works properly" $ do
    boolDemote SFalse @?= False
    boolDemote STrue @?= True

boolPureUnit :: (Applicative m) => SBool p -> m ()
boolPureUnit arg =
  $(sCases ''Bool [|arg|] [|pure ()|])

boolDemote :: SBool p -> Bool
boolDemote arg =
  $(sCases ''Bool [|arg|] [|demote arg|])

data Mode = Pred | Id | Succ
  deriving (Show, Eq, Ord)

deriveAllKnown True ''Mode

class Branch (mode :: Mode) where
  branch :: proxy mode -> Int -> Int

instance Branch Pred where
  branch = const pred

instance Branch Id where
  branch = const id

instance Branch Succ where
  branch = const succ

-- We need this to avoid stage restrictions
pure []

applyMode :: SMode mode -> Int -> Int
applyMode mode n =
  $(sCases ''Mode [|mode|] [|branch mode n|])

test_branching :: TestTree
test_branching = testCase "sCases handles instance resolution properly" $ do
  applyMode SPred 12 @?= 11
  applyMode SId 12 @?= 12
  applyMode SSucc 12 @?= 13
