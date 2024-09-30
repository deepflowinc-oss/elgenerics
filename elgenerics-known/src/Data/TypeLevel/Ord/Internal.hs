{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.TypeLevel.Ord.Internal where

type family CaseOrdering (ord :: Ordering) lt eq gt where
  CaseOrdering 'LT lt _ _ = lt
  CaseOrdering 'EQ _ eq _ = eq
  CaseOrdering 'GT _ _ gt = gt
