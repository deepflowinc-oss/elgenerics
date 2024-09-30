{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Data.Union.Internal where

import Data.Kind (Type)

data Union (h :: k -> Type) (vs :: [k]) where
  Summand :: !Word -> v -> Union h vs
