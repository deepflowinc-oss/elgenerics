{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans -dcore-lint #-}
{-# OPTIONS_GHC -Wno-unused-foralls -Wno-missing-methods #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.List.Solver #-}

module Main where

import Data.Constraint.Operators (All)
import Data.Functor.Compose (Compose (Compose))
import Data.Functor.Identity (Identity (Identity))
import Data.HList.HigherKinded (HList, hfoldMap, hmap)
import Data.Proxy (Proxy (..))
import Data.TypeLevel.List (ElemAt, KnownTyList, Map)
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as GM
import Data.Vector.Unboxed qualified as U

data Dict c where
  Dict :: (c) => Dict c

class Printable a where
  doPrint :: a -> IO ()
  anotherPrint :: a -> IO ()

newtype MyHList h xs = MyHList {runMyHList :: HList h xs}

instance
  (KnownTyList xs, All U.Unbox (Map h xs)) =>
  Printable (MyHList h xs)
  where
  doPrint (MyHList hl) =
    hfoldMap
      ( \(Proxy :: (G.Vector U.Vector (h (ElemAt k xs))) => Proxy k)
         (Proxy :: Proxy x)
         (_ :: h x) ->
            return ()
      )
      hl
  anotherPrint (MyHList hl) =
    hfoldMap
      ( \(Proxy :: Proxy k)
         (Proxy :: Proxy x)
         (_ :: h x) ->
            return ()
      )
      hl

main :: IO ()
main = putStrLn "Everytihng is ok; just to check whether it compiles suffices."

class ToTuple a where
  toTuple :: a -> ()

toTupling ::
  forall h as.
  (All ToTuple (Map h as), KnownTyList as) =>
  HList h as ->
  ()
toTupling =
  hfoldMap $ const $ const toTuple

newtype HL h as = HL {runHL :: HList h as}

data instance U.Vector (HL h as)
  = V_HL !Int !(HList Identity (Map (Compose U.Vector h) as))

data instance U.MVector s (HL h as)
  = MV_HL !Int !(HList Identity (Map (U.MVector s) (Map h as)))

instance
  (KnownTyList as, All U.Unbox (Map h as)) =>
  U.Unbox (HL h as)

instance
  (KnownTyList as, All U.Unbox (Map h as)) =>
  G.Vector U.Vector (HL h as)
  where
  basicUnsafeSlice i n (V_HL _ vs) =
    V_HL n $
      hmap @Identity @Identity
        @(Map (Compose U.Vector h) as)
        @(Map (Compose U.Vector h) as)
        ( \(Proxy :: Proxy k) (Identity (Compose uv)) ->
            Identity $ Compose $ G.basicUnsafeSlice i n uv
        )
        vs

instance
  (KnownTyList as, All U.Unbox (Map h as)) =>
  GM.MVector U.MVector (HL h as)
  where
  basicUnsafeSlice i n (MV_HL _ vs :: U.MVector s (HL h as)) =
    MV_HL n $
      hmap @Identity @Identity
        @(Map (U.MVector s) (Map h as))
        @(Map (U.MVector s) (Map h as))
        ( \(Proxy :: Proxy k) (Identity uv) ->
            Identity $ GM.basicUnsafeSlice i n uv
        )
        vs
