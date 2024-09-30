{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.TypeLevel.OrdMapSpec.Cases where

import Data.Constraint (Dict (Dict))
import Data.TypeLevel.OrdMap
import Helpers (withNoTypeError)
import Test.Inspection qualified as IT

test011_def ::
  Dict
    ( ValidRBTree
        ( FromList
            '[ 20 ::: Int
             , 30 ::: Int
             , 40 ::: Int
             , 50 ::: Int
             , 10 ::: Int
             , 2 ::: Int
             , 0 ::: Int
             , 1 ::: Int
             ]
        )
    )
test011_def = Dict

test011 :: IT.Result
test011 = $(withNoTypeError 'test011_def)

test01_def ::
  Dict
    ( ValidRBTree
        ( FromList
            '[ 1 ::: Int
             , 2 ::: Int
             , 3 ::: Int
             , 4 ::: Int
             , 0 ::: Int
             ]
        )
    )
test01_def = Dict

test01 :: IT.Result
test01 = $(withNoTypeError 'test01_def)

test02_def ::
  Dict
    ( ValidRBTree
        (Insert 2 Int (FromList [0 ::: Int, 1 ::: Int]))
    )
test02_def = Dict

test02 :: IT.Result
test02 = $(withNoTypeError 'test02_def)

test03_def ::
  Dict
    ( ValidRBTree
        (Insert 2 Int (FromList '[0 ::: Int]))
    )
test03_def = Dict

test03 :: IT.Result
test03 = $(withNoTypeError 'test03_def)

test04_def :: Dict (ValidRBTree (FromList '[1 ::: Int, 0 ::: Int]))
test04_def = Dict

test04 :: IT.Result
test04 = $(withNoTypeError 'test04_def)
