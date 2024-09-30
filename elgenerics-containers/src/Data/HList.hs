{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.List.Solver #-}

module Data.HList (
  pattern (:-),
  pattern HNil,
  HList,
  (:<-) (..),
  HasFactor',
  hsingleton,
  happend,
  hsplitAt,
  generate,
  generateM,
  hindex,
  hconcat,
  htoList,
  hzipWithM_,
  hmapM,
  hmapM_,
  hmap,
  hany,
  hfoldMap,
  hslice,
  HasFactors (..),
  HListLike (..),
  CoercedHList (..),
) where

import Data.Constraint
import Data.Constraint.Operators
import Data.Functor.Identity
import Data.HList.HigherKinded qualified as HK
import Data.Kind (Type)
import Data.Membership
import Data.Product.Class
import Data.Proxy
import Data.TypeLevel.List
import Data.TypeLevel.Path
import GHC.Exts
import Unsafe.Coerce

type HList = HK.HList Identity

-- | O(1)
hindex :: forall k as. (KnownNat k) => Proxy k -> HList as -> ElemAt k as
hindex = coerce $ HK.hindex @k @Identity @as

infixr 9 :-

pattern (:-) :: () => (Member a as', as' ~ (a ': as)) => a -> HList as -> HList as'
pattern a :- v = Identity a HK.:- v

pattern HNil :: () => (qs ~ '[]) => HList qs
pattern HNil = HK.HNil

{-# COMPLETE HNil, (:-) #-}

happend :: HList as -> HList bs -> HList (as ++ bs)
happend = HK.happend

generate ::
  forall as.
  (KnownTyList as) =>
  (forall k. (KnownNat k) => Proxy k -> ElemAt k as) ->
  HList as
{-# INLINE generate #-}
generate = \f -> HK.generate (Identity . f)

generateM ::
  forall m as.
  (KnownTyList as, Monad m) =>
  (forall k. (KnownNat k) => Proxy k -> m (ElemAt k as)) ->
  m (HList as)
{-# INLINE generateM #-}
generateM = \f ->
  HK.generateM (fmap Identity . f)

hconcat :: HK.HList HList as -> HList (Concat as)
hconcat = HK.hconcat

htoList ::
  forall as a.
  (forall x. (Member x as) => x -> a) ->
  HList as ->
  [a]
htoList f = HK.htoList @Identity @as @a (f . runIdentity)

hsingleton :: a -> HList '[a]
{-# INLINE hsingleton #-}
hsingleton = HK.hsingleton . Identity

hzipWithM_ ::
  forall m as as'.
  (Monad m) =>
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (ElemAt k as') as'
    ) =>
    Proxy k ->
    ElemAt k as ->
    ElemAt k as' ->
    m ()
  ) ->
  HList as ->
  HList as' ->
  m ()
{-# INLINE hzipWithM_ #-}
hzipWithM_ =
  \f -> HK.hzipWithM_ @_ @_ @m @as @as' (\p (Identity x) (Identity y) -> f p x y)

hmapM ::
  forall m as as'.
  (Monad m) =>
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (ElemAt k as') as'
    ) =>
    Proxy k ->
    ElemAt k as ->
    m (ElemAt k as')
  ) ->
  HList as ->
  m (HList as')
{-# INLINE hmapM #-}
hmapM f =
  HK.hmapM @_ @_ @_ @as @as'
    (\p (Identity x) -> Identity <$> f p x)

hmapM_ ::
  forall m as.
  (Monad m) =>
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    ) =>
    Proxy k ->
    ElemAt k as ->
    m ()
  ) ->
  HList as ->
  m ()
hmapM_ = \f -> HK.hmapM_ @_ @Identity @as (\p -> f p . runIdentity)

hfoldMap ::
  forall as w.
  (Monoid w) =>
  ( forall k x.
    (KnownNat k, Member x as, ElemAt k as ~ x) =>
    Proxy k ->
    Proxy x ->
    x ->
    w
  ) ->
  HList as ->
  w
hfoldMap = \f -> HK.hfoldMap @Identity @as @w $
  \p l -> f p l . runIdentity

hmap ::
  forall as as'.
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (ElemAt k as') as'
    ) =>
    Proxy k ->
    ElemAt k as ->
    ElemAt k as'
  ) ->
  HList as ->
  HList as'
hmap = \f -> HK.hmap (\p -> Identity . f p . runIdentity)

hany ::
  forall as.
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    ) =>
    Proxy k ->
    ElemAt k as ->
    Bool
  ) ->
  HList as ->
  Bool
{-# INLINE hany #-}
hany = \f -> HK.hany (\p -> f p . runIdentity)

instance {-# OVERLAPPING #-} (KnownTyList as, All Show as) => Show (HList as) where
  showsPrec _ HNil = showString "[]"
  showsPrec _ vs =
    showString "["
      . foldr1
        (\a b -> a . showString ", " . b)
        ( htoList
            ( \(x :: (Member x as) => x) ->
                showsPrec 11 x \\ subDict @Show @x @as
            )
            vs
        )
      . showString "]"

hslice ::
  (KnownNatList ns) =>
  pxy ns ->
  HList as ->
  HK.HList HList (Sliced ns as)
hslice = HK.hslice

hsplitAt ::
  (KnownNat n) =>
  pxy n ->
  HList as ->
  (HList (Take n as), HList (Drop n as))
hsplitAt = HK.hsplitAt

class (HasFactor c a) => HasFactor' a c

instance (HasFactor c a) => HasFactor' a c

newtype a :<- b = Flip {runFlipArrow :: b -> a}

class (All (HasFactor' a) (Factors a)) => HasFactors a where
  type Factors a :: [Type]
  type Factors a = GFacts (Rep a)

class (HasFactors a) => HListLike a where
  toHList :: a -> HList (Factors a)
  fromHList :: HList (Factors a) -> a
  default toHList ::
    (Generic a, GHListLike (Rep a), GFacts (Rep a) ~ Factors a) =>
    a ->
    HList (Factors a)
  toHList = gtoHList . from
  default fromHList ::
    (Generic a, GHListLike (Rep a), GFacts (Rep a) ~ Factors a) =>
    HList (Factors a) ->
    a
  fromHList = to . gfromHList

class GHListLike f where
  type GFacts f :: [Type]
  gtoHList :: f () -> HList (GFacts f)
  gfromHList :: HList (GFacts f) -> f ()

instance GHListLike (K1 i c) where
  type GFacts (K1 i c) = '[c]
  gtoHList (K1 a) = hsingleton a
  gfromHList (a :- HNil) = K1 a

instance (GHListLike f) => GHListLike (M1 i c f) where
  type GFacts (M1 i c f) = GFacts f
  gtoHList (M1 f) = gtoHList f
  gfromHList = M1 . gfromHList

instance (KnownTyList (GFacts f), GHListLike f, GHListLike g) => GHListLike (f :*: g) where
  type GFacts (f :*: g) = GFacts f ++ GFacts g
  gtoHList (f :*: g) = happend (gtoHList f) (gtoHList g)
  gfromHList v =
    let (lh, rh) = hsplitAt (Proxy @(Length (GFacts f))) v
     in (gfromHList (unsafeCoerce lh) :*: gfromHList (unsafeCoerce rh))

instance GHListLike U1 where
  type GFacts U1 = '[]
  gtoHList _ = HNil
  gfromHList _ = U1

newtype CoercedHList bs a = CoercedHList {runCoercedHList :: a}
  deriving (Read, Show, Eq, Ord)

instance
  ( Generic a
  , GHListLike (Rep a)
  , Coercible (GFacts (Rep a)) bs
  , All (HasFactor' (CoercedHList bs a)) bs
  ) =>
  HasFactors (CoercedHList bs a)
  where
  type Factors (CoercedHList bs a) = bs

instance
  ( Generic a
  , GHListLike (Rep a)
  , Coercible (GFacts (Rep a)) bs
  , All (HasFactor' (CoercedHList bs a)) bs
  ) =>
  HListLike (CoercedHList bs a)
  where
  toHList = unsafeCoerce . gtoHList . from . runCoercedHList
  fromHList = CoercedHList . to . gfromHList . unsafeCoerce
