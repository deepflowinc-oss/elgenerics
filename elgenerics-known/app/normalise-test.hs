{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.Normalise.Plugin #-}

module Main where

import Data.TypeLevel.Normalise.Plugin
import Data.TypeLevel.OrdMap (FromList, (:::))
import NormDefs

type ADict a b c d e =
  Normalise
    (FromList '[E ::: a, D ::: b, C ::: c, A ::: d, B ::: e])

data Foo a b = Foo

type OneTwoDict = ADict0 1 2 3 4 5

type TyDict = ADict0 Int String Bool (Maybe Bool) ()

class MyMap ty

instance MyMap TyDict

instance MyMap OneTwoDict

main :: IO ()
main = return ()
