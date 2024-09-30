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

module Data.Record.Builder.HigherKindedSpec where

import Data.Record.Builder.HigherKinded qualified as B
import Data.Record.Cases
import Data.Record.HigherKinded (
  Fields,
  OnEntry (OnEntry),
  fromHRecord',
  fromRecord,
  (:=) (..),
 )
import Data.Tagged (Tagged (Tagged))
import Test.QuickCheck ((===))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)

test_Buz0 :: TestTree
test_Buz0 =
  testGroup
    "Builds fixed record into native record properly"
    [ testProperty "Simple" \buz0@Buz0 {..} ->
        fromRecord @Buz0 @(Fields Buz0)
          ( B.build $
              B.empty
                B.&+ #ddd
                := Tagged ddd
                B.&+ #ggg
                := Tagged ggg
          )
          === buz0
    , testProperty "Higher-Kinded" \buz0@Buz0 {..} ->
        fromHRecord'
          ( B.build $
              B.empty
                B.&+ #ddd
                := OnEntry ddd
                B.&+ #ggg
                := OnEntry ggg
          )
          === buz0
    ]
