{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin Data.Record.Plugin #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.List.Overloaded #-}
{-# OPTIONS_GHC -fplugin-opt Data.Record.Plugin:MyRecord #-}

module Main where

import Data.Record.HigherKinded (IsHRecord (..))
import Data.Record.HigherKinded qualified as HK
import GHC.Generics (Generic)

-- 以下のデータ型自体はテストでは用いられていない。
-- しかし、コンパイルが現実的な時間で通ること自体がテストの意図になっている。

data ManyFields = ManyFields
  { mf2 :: String
  , mf5 :: Int
  , mf6 :: String
  , mf7 :: Int
  , mf1 :: Int
  , mf8 :: String
  , mf10 :: String
  , mf11 :: Int
  , mf3 :: Int
  , mf12 :: String
  , mf13 :: String
  , mf4 :: String
  , mf14 :: String
  , mf9 :: Int
  , mf15 :: String
  }
  deriving (Generic)
  deriving anyclass (IsHRecord HK.STagged)

main :: IO ()
main = putStrLn "Finished!"
