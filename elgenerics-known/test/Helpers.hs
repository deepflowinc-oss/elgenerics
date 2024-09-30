{-# LANGUAGE TemplateHaskell #-}

module Helpers (
  shouldThrowTypeError,
  shouldNotThrowTypeError,
  testInspection,
  expectInspectionFail,
  withNoTypeError,
) where

import Control.DeepSeq (NFData, force)
import Control.Exception (
  TypeError (TypeError),
  evaluate,
  try,
 )
import Control.Exception.Base (typeError)
import Language.Haskell.TH (ExpQ)
import Language.Haskell.TH.Syntax (Name)
import Test.Inspection (doesNotUse, inspectTest)
import Test.Inspection qualified as IT
import Test.Tasty (TestTree)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase)

shouldThrowTypeError :: (Show a, NFData a) => a -> Assertion
shouldThrowTypeError inp = do
  eith <- try $ evaluate $ force inp
  case eith of
    Left TypeError {} -> pure ()
    Right a ->
      assertFailure $
        "Deferred type error expected, but got a value: "
          <> show a

shouldNotThrowTypeError :: (Show a, NFData a) => a -> Assertion
shouldNotThrowTypeError inp = do
  eith <- try $ evaluate $ force inp
  case eith of
    Left te@TypeError {} ->
      assertFailure $
        "No type error expected, but got: " <> show te
    Right {} -> pure ()

testInspection ::
  String -> IT.Result -> TestTree
testInspection lab resl = testCase lab $
  case resl of
    IT.Success {} -> pure ()
    IT.Failure msg -> assertFailure msg

expectInspectionFail ::
  String -> IT.Result -> TestTree
expectInspectionFail lab resl = testCase lab $
  case resl of
    IT.Success msg ->
      assertFailure $
        "Inspection expected to fail, but succeeded with the following msg: "
          <> msg
    IT.Failure {} -> pure ()

withNoTypeError :: Name -> ExpQ
withNoTypeError n = inspectTest $ n `doesNotUse` 'typeError
