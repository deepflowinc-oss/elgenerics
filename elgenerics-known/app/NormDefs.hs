{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.Normalise.Plugin #-}

module NormDefs where

import Data.Proxy
import Data.TypeLevel.Ord
import Data.TypeLevel.OrdMap (FromList, (:::))
import Data.TypeLevel.Typeable
import Data.Typeable
import GHC.Generics (Generic)

data FTags = A | B | C | D | E
  deriving (Generic, Show, Typeable)

type A = 'A

type B = 'B

type C = 'C

type D = 'D

type E = 'E

deriveTypeRep ''FTags

instance POrd FTags where
  type Compare l r = Compare (Proxy l) (Proxy r)

type ADict0 a b c d e =
  FromList '[E ::: a, D ::: b, C ::: c, A ::: d, B ::: e]
