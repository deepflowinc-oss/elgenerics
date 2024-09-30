{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Data.Constraint.Operators (
  All,
  Prod,
  Trivially,
  MaybeC,
  withAllFromMember,
  collectAllDict,
  elimByAll,
  genDicts,
  ElemDict (..),
  reifyDict,
  DeferrableFor,
  undefer,
  presentDict,
  superDict,
  deferViaSuper,
  deferWith,
  ReifiedDeferrable (..),
  withTailMember,
  module Data.Constraint.TH,
  deferAllWithDict,
  elimFromMaybeC,
  elimFromMaybeC',
  CustomDict (..),
) where

import Data.Constraint
import Data.Constraint.Deferrable
import Data.Constraint.TH
import Data.Functor ((<&>))
import Data.Proxy
import Data.TypeLevel.Known (Known (..))
import Data.TypeLevel.Known.TH (sCases)
import Data.TypeLevel.List.Core
import Data.TypeLevel.List.Unsafe
import Data.TypeLevel.Maybe (FromMaybe)
import GHC.Exts
import GHC.TypeNats
import Unsafe.Coerce

type family Prod (c :: [k -> Constraint]) (a :: k) :: Constraint where
  Prod '[] _ = ()
  Prod (c ': cs) v = (c v, Prod cs v)

type family Trivially a :: Constraint where
  Trivially _ = ()

type family MaybeC (c :: k -> Constraint) (mk :: Maybe k) :: Constraint where
  MaybeC _ 'Nothing = ()
  MaybeC c ('Just a) = c a

data ElemDict (c :: k -> Constraint) (xs :: [k]) where
  ElemDict :: Proxy# x -> !Natural -> Dict (c x) -> ElemDict c xs

-- 素直に型クラスだけを使った @All@ の定義では、
-- @All c (x ': xs)@ から @All c xs@ を推論するのが不可能になる。
-- これは、インスタンス解決において、インスタンスに付いている文脈は
-- 解決後消去されるという挙動による（この挙動は OVERLAPPING や
-- Flexible Instancesの事を考えると自然である）。
-- しかし、それでは余りに @'All'@ 制約が使いづらくなってしまうため、
-- 相互再帰的に「前までの辞書の情報を全部持っている」という気持ちを、
-- @All'@ 型族によって表現して、@All@ の親クラス制約としている。
type family All' (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All' _ '[] = ()
  All' c (x ': xs) = (c x, All c xs)

class (All' c xs) => All (c :: k -> Constraint) (xs :: [k]) where
  nthElemDict :: Natural -> Proxy# xs -> Int -> ElemDict c xs
  genDicts' :: Natural -> Proxy# xs -> [ElemDict c xs]

instance All c '[] where
  nthElemDict _ _ _ = error "nthElemDict for empty list"
  {-# INLINE nthElemDict #-}
  genDicts' _ _ = []
  {-# INLINE genDicts' #-}

instance (All c xs, c x) => All c (x ': xs) where
  nthElemDict !k _ !n
    | n == 0 = ElemDict (proxy# :: Proxy# x) k $ Dict @(c x)
    | otherwise = unsafeCoerce $ nthElemDict @_ @c @xs (k + 1) proxy# (n - 1)
  {-# INLINE nthElemDict #-}
  genDicts' !n _ =
    ElemDict (proxy# :: Proxy# x) n (Dict @(c x))
      : unsafeCoerce (genDicts' @_ @c @xs (n + 1) proxy#)
  {-# INLINE genDicts' #-}

data AllDict c (x :: k) (xs :: [k]) where
  There :: (c x) => AllDict c x xs

reifyDict ::
  forall k c (x :: k) xs.
  (Member x xs, All c xs) =>
  AllDict c x xs
reifyDict =
  let n = fromIntegral $ natVal' @(Index x xs) proxy#
   in case nthElemDict @_ @c @xs 0 proxy# n of
        ElemDict _ _ (unsafeCoerce @_ @(Dict (c x)) -> Dict) -> There

elimByAll ::
  forall c x xs r.
  (All c xs, Member x xs) =>
  ((c x) => r) ->
  r
elimByAll f = case reifyDict @_ @c @x @xs of
  There -> f

genDicts :: forall c xs. (All c xs) => [ElemDict c xs]
genDicts = genDicts' @_ @c @xs 0 proxy#

class (Deferrable (c a)) => DeferrableFor c a

instance (Deferrable (c a)) => DeferrableFor c a

instance
  (KnownTyList xs, All (DeferrableFor c) xs) =>
  Deferrable (All c xs)
  where
  deferEither (_ :: proxy (All c xs)) f =
    go 0 (tyListSkeleton @xs) <&> \Dict -> f
    where
      go ::
        (All (DeferrableFor c) ys) =>
        Int ->
        PList ys ->
        Either String (Dict (All c ys))
      go !_ PNil = Right Dict
      go !n (PCons (_ :: Proxy# y) sxs) =
        case deferEither_ @(c y) @(Dict (c y)) Dict of
          Left err ->
            Left $
              show n
                ++ "th element of the given type-level list fails to satisfy constraint; "
                ++ err
          Right Dict -> go (n + 1) sxs <&> \Dict -> Dict

-- Orphan instances for n-tuples of constraints
fmap concat $ mapM deriveTupleDeferrable [2 .. 62]

undefer :: forall p r. (p) => ((Deferrable p) => r) -> r
undefer = deferWith $ presentDict @p

deferAllWithDict ::
  forall c xs.
  (KnownTyList xs) =>
  (forall x. (Member x xs) => Proxy x -> Either String (Dict (c x))) ->
  Either String (Dict (All c xs))
deferAllWithDict = go $ tyListSkeleton @xs
  where
    go ::
      PList ys ->
      (forall x. (Member x ys) => Proxy x -> Either String (Dict (c x))) ->
      Either String (Dict (All c ys))
    go PNil _ = Right Dict
    go (PCons (_ :: Proxy# x) (ys :: PList ys)) deferrer = do
      let def' :: forall z. (Member z ys) => Proxy z -> Either String (Dict (c z))
          def' = withTailMember @z @ys @x deferrer
      Dict <- go ys def'
      Dict <- deferrer @x Proxy
      pure Dict

deferViaSuper ::
  forall c d r.
  ((c) => d, Deferrable c) =>
  ((Deferrable d) => r) ->
  r
deferViaSuper = deferWith $ superDict @c @d

newtype WithDeferred p r
  = WithDeferred ((Deferrable p) => r)

newtype ReifiedDeferrable (c :: Constraint)
  = ReifiedDeferrable
      (forall proxy r. proxy c -> ((c) => r) -> Either String r)

deferWith ::
  forall c r.
  ReifiedDeferrable c ->
  ((Deferrable c) => r) ->
  r
deferWith def wd =
  (unsafeCoerce (WithDeferred @c @r wd) :: ReifiedDeferrable c -> r)
    def

presentDict :: (c) => ReifiedDeferrable c
presentDict = ReifiedDeferrable $ \_ act -> Right act

superDict :: forall c d. ((c) => d, Deferrable c) => ReifiedDeferrable d
superDict = ReifiedDeferrable $ \_ act -> deferEither_ @c act

withAllFromMember ::
  forall c xs r.
  (KnownTyList xs) =>
  (forall x. (Member x xs) => Proxy x -> Dict (c x)) ->
  ((All c xs) => r) ->
  r
withAllFromMember f = withDict (collectAllDict @c @xs f)

collectAllDict ::
  forall c xs.
  (KnownTyList xs) =>
  (forall x. (Member x xs) => Proxy x -> Dict (c x)) ->
  Dict (All c xs)
collectAllDict = go $ tyListSkeleton @xs
  where
    go ::
      PList ys ->
      (forall x. (Member x ys) => Proxy x -> Dict (c x)) ->
      Dict (All c ys)
    go PNil _ = Dict
    go (PCons (_ :: Proxy# x) (ys :: PList ys)) f =
      let f' :: forall z. (Member z ys) => Proxy z -> Dict (c z)
          f' = withTailMember @z @ys @x f
       in case (f @x Proxy, go ys f') of
            (Dict, Dict) -> Dict

withTailMember ::
  forall z ys w r.
  (Member z ys) =>
  ((Member z (w ': ys)) => r) ->
  r
withTailMember =
  unsafeWithKnownMember @z @(w ': ys)
    (fromIntegral $ natVal @(Index z ys) Proxy + 1)

elimFromMaybeC ::
  forall c x m r.
  (c x, MaybeC c m, Known m) =>
  ((c (FromMaybe x m)) => r) ->
  r
{-# INLINE elimFromMaybeC #-}
elimFromMaybeC = $(sCases ''Maybe [|sKnownVal' @m|] [|\act -> act|])

-- | a variant of 'elimFromMaybeC' with all the kinds are explicitly quantified and returns custom dict.
elimFromMaybeC' ::
  forall k (c :: k -> Constraint) (x :: k) (m :: Maybe k).
  (c x, MaybeC c m, Known m) =>
  CustomDict (c (FromMaybe x m))
{-# INLINE elimFromMaybeC' #-}
elimFromMaybeC' = elimFromMaybeC @c @x @m CDict

data CustomDict c where
  CDict :: (c) => CustomDict c
