{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans -dcore-lint #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.List.Solver #-}

module Data.HList.HigherKinded (
  HList ((:-), HNil),
  HListView (..),
  viewHList,
  hsingleton,
  castAppliedCon,
  happend,
  hsplitAt,
  factorIdentity,
  hfoldMap,
  hfoldr,
  hfoldl',
  purify,
  purifyApply,
  innerComp,
  factor,
  generateM,
  generateA,
  generate,
  hix,
  hindex,
  hconcat,
  htoList,
  hzip,
  hzipWithM,
  hzipWith,
  hzipWithM_,
  hzipWith3,
  hzipWithM3,
  hunzip,
  hunzip',
  hunzipWith,
  hunzipWithM,
  hmapM,
  hmapM_,
  htraverse_,
  hmap,
  htraverse,
  hany,
  hall,
  liftHList,
  hslice,
  hset,
  hset',
  hmodify,
  hmodify',
) where

import Control.Arrow
import Control.DeepSeq
import Control.Lens (Lens', lens)
import Control.Monad.Primitive
import Data.Constraint hiding ((***))
import Data.Constraint.Operators
import Data.Foldable qualified as F
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.HList.Internal
import Data.Membership
import Data.Monoid (Endo (..))
import Data.Monoid qualified as Mon
import Data.Proxy
import Data.Type.Equality
import Data.TypeLevel.Function
import Data.TypeLevel.List
import Data.TypeLevel.Ord ()
import Data.TypeLevel.OrdMap ()
import Data.Vector qualified as V
import Data.Vector.Fusion.Bundle.Monadic qualified as FV
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as M
import Data.Vector.Mutable qualified as MV
import Data.Vector.Unboxed qualified as U
import GHC.Exts
import Unsafe.Coerce

-- | O(1)
hindex :: (KnownNat k) => Proxy k -> HList h as -> h (ElemAt k as)
hindex k = unsafeCoerce $ flip V.unsafeIndex $ fromIntegral $ natVal k

unconsV :: V.Vector a -> Maybe (a, V.Vector a)
unconsV v =
  if V.null v
    then Nothing
    else Just (V.unsafeHead v, V.unsafeTail v)

data HListView h as where
  HNilV :: HListView h '[]
  HConsV :: h a -> HList h as -> HListView h (a ': as)

viewHList :: forall h as. HList h as -> HListView h as
{-# NOINLINE viewHList #-} -- NOTE: See https://gitlab.haskell.org/ghc/ghc/issues/16893
viewHList (HL v) =
  case unconsV v of
    Nothing -> unsafeCoerce HNilV
    Just (a, vs) -> unsafeCoerce $ HConsV (unsafeCoerce a) $ HL vs

liftHList :: (forall a. f a -> g a) -> HList f as -> HList g as
liftHList f = hmap (const f)

infixr 9 :-

pattern (:-) :: () => (Member a as', as' ~ (a ': as)) => h a -> HList h as -> HList h as'
pattern a :- v <-
  (viewHList -> HConsV a v)
  where
    a :- (HL v) = HL (V.cons (unsafeCoerce a) v)

pattern HNil :: () => (qs ~ '[]) => HList h qs
pattern HNil <-
  (viewHList -> HNilV)
  where
    HNil = HL V.empty

{-# COMPLETE HNil, (:-) #-}

generate ::
  forall h as.
  (KnownTyList as) =>
  ( forall n.
    ( KnownNat n
    , Member (h (ElemAt n as)) (Map h as)
    , Member (ElemAt n as) as
    ) =>
    Proxy n ->
    h (ElemAt n as)
  ) ->
  HList h as
generate f =
  HL $
    V.generate (fromIntegral $ tyListLength @(Map h as)) $ \i ->
      withKnownNat (fromIntegral i) $ \(p :: Proxy n) ->
        unsafeCoerce $ f p

generateA ::
  forall f h as.
  (Applicative f, KnownTyList as) =>
  ( forall n.
    ( KnownNat n
    , Member (h (ElemAt n as)) (Map h as)
    , Member (ElemAt n as) as
    ) =>
    Proxy n ->
    f (h (ElemAt n as))
  ) ->
  f (HList h as)
generateA f =
  fmap HL $
    sequenceA $
      V.generate (fromIntegral $ tyListLength @(Map h as)) $ \i ->
        withKnownNat (fromIntegral i) $
          fmap (unsafeCoerce @_ @Any) . f

generateM ::
  forall m h as.
  (Monad m, KnownTyList as) =>
  ( forall k.
    (KnownNat k, Member (ElemAt k as) as) =>
    Proxy k ->
    m (h (ElemAt k as))
  ) ->
  m (HList h as)
generateM f =
  fmap HL $
    V.generateM (fromIntegral $ tyListLength @(Map h as)) $ \i ->
      withKnownNat (fromIntegral i) $ fmap unsafeCoerce . f

hconcat :: HList (HList h) as -> HList h (Concat as)
hconcat = HL . F.fold . unsafeCoerce @_ @(V.Vector (V.Vector Any))

happend :: HList h as -> HList h bs -> HList h (as ++ bs)
happend (HL v) (HL u) = HL $ v V.++ u

purify :: HList f as -> HList Identity (Map f as)
purify = unsafeCoerce

purifyApply :: HList (Applied f) as -> HList Identity (MapApply f as)
purifyApply = unsafeCoerce

innerComp ::
  HList (Applied (f .: g)) as ->
  HList (Applied f) (MapApply g as)
innerComp = unsafeCoerce

castAppliedCon ::
  HList (Applied (Con h)) as ->
  HList h as
castAppliedCon = unsafeCoerce

factor :: forall g as f. HList f (Map g as) -> HList (Applied (Con f .: Con g)) as
factor = unsafeCoerce

factorIdentity ::
  HList Identity (MapApply f as) ->
  HList (Applied f) as
factorIdentity = unsafeCoerce

htoList ::
  forall h as a.
  (forall x. (Member x as, Member (h x) (Map h as)) => h x -> a) ->
  HList h as ->
  [a]
htoList f (HL v) =
  V.toList $
    V.imap
      ( \i x ->
          withKnownNat (fromIntegral i) $ \(Proxy :: Proxy i) ->
            f (unsafeCoerce x :: h (ElemAt i as))
      )
      v

hsingleton :: h a -> HList h '[a]
hsingleton = HL . V.singleton . unsafeCoerce

data instance U.Vector (HList h as)
  = V_HList !Int !(HList (Compose U.Vector h) as)

data instance U.MVector s (HList h as)
  = MV_HList !Int !(HList (Compose (U.MVector s) h) as)

instance
  (All NFData (Map h as), KnownTyList as) =>
  NFData (HList h as)
  where
  rnf =
    hfoldr
      (\(_ :: Proxy k) _ a b -> rnf a `seq` b)
      ()

instance
  (All U.Unbox (Map h as), KnownTyList as) =>
  U.Unbox (HList h as)

instance
  (All U.Unbox (Map h as), KnownTyList as) =>
  G.Vector U.Vector (HList h as)
  where
  basicUnsafeFreeze (MV_HList n vs) =
    V_HList n
      <$> hmapM
        ( \(Proxy :: Proxy k) (Compose v) -> do
            unsafeCoerce <$> G.basicUnsafeFreeze v
        )
        vs
  basicUnsafeThaw (V_HList n vs) =
    MV_HList n
      <$> hmapM
        ( \(Proxy :: Proxy k) (Compose e) -> do
            Compose <$> G.basicUnsafeThaw e
        )
        vs
  basicLength (V_HList l _) = l
  basicUnsafeIndexM (V_HList _ vs) i =
    hmapM @_ @_ @_ @as @as
      ( \(Proxy :: Proxy k) (Compose uv) ->
          G.basicUnsafeIndexM
            (uv :: U.Vector (h (ElemAt k as)))
            i
      )
      vs

  basicUnsafeSlice i n (V_HList _ vs) =
    V_HList n $
      hmap
        ( \(Proxy :: Proxy k) (Compose uv) ->
            Compose $ G.basicUnsafeSlice i n uv
        )
        vs

instance
  (All U.Unbox (Map h as), KnownTyList as) =>
  M.MVector U.MVector (HList h as)
  where
  basicLength (MV_HList n _) = n

  basicUnsafeNew ::
    forall m.
    (PrimMonad m) =>
    Int ->
    m (U.MVector (PrimState m) (HList h as))
  basicUnsafeNew n =
    fmap (MV_HList n) $
      generateM $ \(Proxy :: Proxy k) ->
        Compose <$> M.basicUnsafeNew @U.MVector @(h (ElemAt k as)) n

  basicUnsafeRead ::
    forall m.
    (PrimMonad m) =>
    U.MVector (PrimState m) (HList h as) ->
    Int ->
    m (HList h as)
  basicUnsafeRead (MV_HList _ v) i =
    hmapM
      ( \(Proxy :: Proxy k) (Compose u) ->
          M.basicUnsafeRead u i
      )
      v

  basicUnsafeWrite ::
    forall m.
    (PrimMonad m) =>
    U.MVector (PrimState m) (HList h as) ->
    Int ->
    HList h as ->
    m ()
  basicUnsafeWrite (MV_HList _ vs) i xs =
    hzipWithM_
      ( \(Proxy :: Proxy i) (Compose v) x ->
          M.basicUnsafeWrite @U.MVector v i x
      )
      vs
      xs

  basicInitialize ::
    forall m.
    (PrimMonad m) =>
    U.MVector (PrimState m) (HList h as) ->
    m ()
  basicInitialize (MV_HList _ vs) =
    hmapM_
      ( \(Proxy :: Proxy k) ->
          M.basicInitialize . getCompose
      )
      vs
  basicUnsafeSlice ::
    forall s.
    Int ->
    Int ->
    U.MVector s (HList h as) ->
    U.MVector s (HList h as)
  basicUnsafeSlice i n (MV_HList _ vs) =
    MV_HList n $
      hmap
        (\(Proxy :: Proxy k) (Compose uv) -> Compose $ M.basicUnsafeSlice i n uv)
        vs

  basicOverlaps ::
    forall s.
    U.MVector s (HList h as) ->
    U.MVector s (HList h as) ->
    Bool
  basicOverlaps
    (MV_HList _ vs)
    (MV_HList _ us) =
      hany
        ( \(Proxy :: Proxy k) (Pair (Compose fx) (Compose gx)) ->
            (M.basicOverlaps @U.MVector @(h (ElemAt k as)) @s fx gx)
        )
        $ hzip vs us

hzip ::
  HList f as -> HList g as -> HList (Product f g) as
{-# INLINE [1] hzip #-}
hzip = \(HL as) (HL bs) ->
  HL $
    V.zipWith
      (\fa gb -> unsafeCoerce $ Pair (fa, gb))
      as
      bs

hzipWith ::
  forall f bs h g as as'.
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (h (ElemAt k as)) (Map h as)
    , Member (ElemAt k as') as'
    , Member (g (ElemAt k as')) (Map g as')
    , Member (ElemAt k bs) bs
    , Member (f (ElemAt k bs)) (Map f bs)
    ) =>
    Proxy k ->
    h (ElemAt k as) ->
    g (ElemAt k as') ->
    f (ElemAt k bs)
  ) ->
  HList h as ->
  HList g as' ->
  HList f bs
{-# INLINE hzipWith #-}
hzipWith f = \(HL as) (HL bs) ->
  HL $
    V.izipWith
      ( \(fromIntegral -> i) a b ->
          withKnownNat i $ \p@(Proxy :: Proxy i) ->
            unsafeCoerce @_ @Any $
              f p (unsafeCoerce a) (unsafeCoerce b)
      )
      as
      bs

hzipWithM ::
  forall f bs h g as as' m.
  (Monad m) =>
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (h (ElemAt k as)) (Map h as)
    , Member (ElemAt k as') as'
    , Member (g (ElemAt k as')) (Map g as')
    , Member (ElemAt k bs) bs
    , Member (f (ElemAt k bs)) (Map f bs)
    ) =>
    Proxy k ->
    h (ElemAt k as) ->
    g (ElemAt k as') ->
    m (f (ElemAt k bs))
  ) ->
  HList h as ->
  HList g as' ->
  m (HList f bs)
{-# INLINE hzipWithM #-}
hzipWithM f (HL v) (HL u) =
  fmap HL $
    V.izipWithM
      ( \(fromIntegral -> k) a b ->
          withKnownNat k $ \p@(Proxy :: Proxy k) ->
            let ek = unsafeCoerce a :: h (ElemAt k as)
                el = unsafeCoerce b :: g (ElemAt k as')
             in unsafeCoerce <$> f p ek el
      )
      v
      u

hzipWithM3 ::
  forall f bs h g l as as' as'' m.
  (Monad m) =>
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (h (ElemAt k as)) (Map h as)
    , Member (ElemAt k as') as'
    , Member (g (ElemAt k as')) (Map g as')
    , Member (ElemAt k as'') as''
    , Member (l (ElemAt k as'')) (Map l as'')
    , Member (ElemAt k bs) bs
    , Member (f (ElemAt k bs)) (Map f bs)
    ) =>
    Proxy k ->
    h (ElemAt k as) ->
    g (ElemAt k as') ->
    l (ElemAt k as'') ->
    m (f (ElemAt k bs))
  ) ->
  HList h as ->
  HList g as' ->
  HList l as'' ->
  m (HList f bs)
{-# INLINE hzipWithM3 #-}
hzipWithM3 f (HL v) (HL u) (HL w) =
  fmap HL $
    G.unstreamM $
      FV.zipWith3M
        ( \(fromIntegral -> k, a) b c ->
            withKnownNat k $ \p@(Proxy :: Proxy k) ->
              let ek = unsafeCoerce a :: h (ElemAt k as)
                  el = unsafeCoerce b :: g (ElemAt k as')
                  eo = unsafeCoerce c :: l (ElemAt k as'')
               in unsafeCoerce <$> f p ek el eo
        )
        (FV.indexed $ FV.fromVector v)
        (FV.fromVector u)
        (FV.fromVector w)

hzipWith3 ::
  forall f bs h g l as as' as''.
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (h (ElemAt k as)) (Map h as)
    , Member (ElemAt k as') as'
    , Member (g (ElemAt k as')) (Map g as')
    , Member (ElemAt k as'') as''
    , Member (l (ElemAt k as'')) (Map l as'')
    , Member (ElemAt k bs) bs
    , Member (f (ElemAt k bs)) (Map f bs)
    ) =>
    Proxy k ->
    h (ElemAt k as) ->
    g (ElemAt k as') ->
    l (ElemAt k as'') ->
    f (ElemAt k bs)
  ) ->
  HList h as ->
  HList g as' ->
  HList l as'' ->
  HList f bs
{-# INLINE hzipWith3 #-}
hzipWith3 f (HL v) (HL u) (HL w) =
  HL $
    V.izipWith3
      ( \(fromIntegral -> k) a b c ->
          withKnownNat k $ \p@(Proxy :: Proxy k) ->
            let ek = unsafeCoerce a :: h (ElemAt k as)
                el = unsafeCoerce b :: g (ElemAt k as')
                eo = unsafeCoerce c :: l (ElemAt k as'')
             in unsafeCoerce $ f p ek el eo
      )
      v
      u
      w

hzipWithM_ ::
  forall h g m as as'.
  (Monad m) =>
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (h (ElemAt k as)) (Map h as)
    , Member (ElemAt k as') as'
    , Member (g (ElemAt k as')) (Map g as')
    ) =>
    Proxy k ->
    h (ElemAt k as) ->
    g (ElemAt k as') ->
    m ()
  ) ->
  HList h as ->
  HList g as' ->
  m ()
{-# INLINE hzipWithM_ #-}
hzipWithM_ f = \(HL as) (HL bs) ->
  V.izipWithM_
    ( \(fromIntegral -> i) a b ->
        withKnownNat i $ \p@(Proxy :: Proxy i) ->
          f p (unsafeCoerce a) (unsafeCoerce b)
    )
    as
    bs

hsplitAt ::
  forall n h as pxy.
  (KnownNat n) =>
  pxy n ->
  HList h as ->
  (HList h (Take n as), HList h (Drop n as))
hsplitAt p (HL v) =
  let (lh, rh) = V.splitAt (fromIntegral $ natVal p) v
   in (HL lh, HL rh)

hmapM ::
  forall m h g as as'.
  (Monad m) =>
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (h (ElemAt k as)) (Map h as)
    , Member (ElemAt k as') as'
    , Member (g (ElemAt k as')) (Map g as')
    ) =>
    Proxy k ->
    h (ElemAt k as) ->
    m (g (ElemAt k as'))
  ) ->
  HList h as ->
  m (HList g as')
hmapM f (HL v) =
  fmap HL $
    flip V.imapM v $ \(fromIntegral -> k) a ->
      withKnownNat k $ \p@(Proxy :: Proxy k) -> do
        let ek = unsafeCoerce a :: h (ElemAt k as)
        unsafeCoerce <$> f p ek

hmapM_ ::
  forall m h as.
  (Monad m) =>
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (h (ElemAt k as)) (Map h as)
    ) =>
    Proxy k ->
    h (ElemAt k as) ->
    m ()
  ) ->
  HList h as ->
  m ()
hmapM_ f (HL v) =
  flip V.imapM_ v $ \(fromIntegral -> k) a ->
    withKnownNat k $ \p@(Proxy :: Proxy k) ->
      f p (unsafeCoerce a :: h (ElemAt k as))

hmap ::
  forall h g as as'.
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (h (ElemAt k as)) (Map h as)
    , Member (ElemAt k as') as'
    , Member (g (ElemAt k as')) (Map g as')
    ) =>
    Proxy k ->
    h (ElemAt k as) ->
    g (ElemAt k as')
  ) ->
  HList h as ->
  HList g as'
hmap f (HL v) =
  HL $
    flip V.imap v $ \(fromIntegral -> k) a ->
      withKnownNat k $ \p@(Proxy :: Proxy k) ->
        let ek = unsafeCoerce a :: h (ElemAt k as)
         in unsafeCoerce $ f p ek

hany ::
  forall h as.
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (h (ElemAt k as)) (Map h as)
    ) =>
    Proxy k ->
    h (ElemAt k as) ->
    Bool
  ) ->
  HList h as ->
  Bool
hany f (HL v) =
  V.any
    ( \(fromIntegral -> k, a) ->
        withKnownNat k $ \p@(Proxy :: Proxy k) ->
          f p (unsafeCoerce a :: h (ElemAt k as))
    )
    $ V.indexed v

hall ::
  forall h as.
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (h (ElemAt k as)) (Map h as)
    ) =>
    Proxy k ->
    h (ElemAt k as) ->
    Bool
  ) ->
  HList h as ->
  Bool
hall f (HL v) =
  V.all
    ( \(fromIntegral -> k, a) ->
        withKnownNat k $ \p@(Proxy :: Proxy k) ->
          f p (unsafeCoerce a :: h (ElemAt k as))
    )
    $ V.indexed v

instance
  (KnownTyList as, All Show (Map h as)) =>
  Show (HList h as)
  where
  showsPrec _ HNil = showString "[]"
  showsPrec _ vs =
    showString "["
      . foldr1
        (\a b -> a . showString ", " . b)
        ( htoList
            ( \(x :: h x) ->
                showsPrec 11 x \\ subDict @Show @(h x) @(Map h as)
            )
            vs
        )
      . showString "]"

instance
  ( KnownTyList as
  , All Eq (Map h as)
  , All Ord (Map h as)
  ) =>
  Ord (HList h as)
  where
  compare =
    fmap
      ( hfoldMap $
          \(Proxy :: Proxy k) (Proxy :: Proxy x) ->
            castWith (elemAtReplicate @(Length as) @k @Ordering) . runIdentity
      )
      . hzipWith @Identity @(Replicate (Length as) Ordering)
        ( \(Proxy :: (KnownNat k) => Proxy k) ->
            fmap
              (Identity . castWith (sym $ elemAtReplicate @(Length as) @k @Ordering))
              . compare
        )

instance
  (KnownTyList as, All Eq (Map h as)) =>
  Eq (HList h as)
  where
  hs == ls =
    Mon.getAll
      $ hfoldMap
        ( \(Proxy :: Proxy k) (Proxy :: Proxy x) ->
            Mon.All
              . castWith (elemAtReplicate @(Length as) @k @Bool)
              . runIdentity
        )
      $ hzipWith @Identity @(Replicate (Length as) Bool)
        ( \(Proxy :: Proxy k)
           a
           b ->
              Identity $
                castWith (sym $ elemAtReplicate @(Length as) @k @Bool) $
                  a == b
        )
        hs
        ls

  hs /= ls =
    Mon.getAny
      $ hfoldMap
        (\(Proxy :: Proxy k) _ -> Mon.Any . castWith (elemAtReplicate @(Length as) @k @Bool) . runIdentity)
      $ hzipWith @Identity @(Replicate (Length as) Bool)
        ( \(Proxy :: Proxy k)
           a
           b ->
              Identity $
                castWith (sym $ elemAtReplicate @(Length as) @k @Bool) $
                  a /= b
        )
        hs
        ls

hslice ::
  forall ns f as pxy.
  (KnownNatList ns) =>
  pxy ns ->
  HList f as ->
  HList (HList f) (Sliced ns as)
hslice _ (HL vec) = HL $ V.fromList $ go (natListVal $ Proxy @ns) vec
  where
    go [] _ = []
    go (n : ns) v =
      let (ls, rs) = V.splitAt (fromIntegral n) v
       in (unsafeCoerce (HL ls) :: Any) : go ns rs

hix :: forall x xs h. (Member x xs) => Lens' (HList h xs) (h x)
hix = lens (hindex (Proxy @(Index x xs))) (flip $ hset (Proxy @(Index x xs)))

hset ::
  (KnownNat k) =>
  Proxy k ->
  h (ElemAt k xs) ->
  HList h xs ->
  HList h xs
hset k x (HL vec) =
  HL $
    V.modify
      ( \mv ->
          MV.unsafeWrite mv (fromIntegral $ natVal k) $ unsafeCoerce x
      )
      vec

hset' ::
  (KnownNat k) =>
  Proxy k ->
  h a ->
  HList h xs ->
  HList h (Take k xs ++ (a ': Drop (k + 1) xs))
hset' k x (HL vec) =
  HL $
    V.modify
      ( \mv ->
          MV.unsafeWrite mv (fromIntegral $ natVal k) $ unsafeCoerce x
      )
      vec

hmodify ::
  (KnownNat k) =>
  Proxy k ->
  (h (ElemAt k xs) -> h (ElemAt k xs)) ->
  HList h xs ->
  HList h xs
hmodify k f (HL vec) =
  HL $
    V.modify
      ( \mv ->
          MV.unsafeModify mv (unsafeCoerce . f . unsafeCoerce) (fromIntegral $ natVal k)
      )
      vec

hmodify' ::
  (KnownNat k) =>
  Proxy k ->
  (h (ElemAt k xs) -> h a) ->
  HList h xs ->
  HList h (Take k xs ++ (a ': Drop (k + 1) xs))
hmodify' k f (HL vec) =
  HL $
    V.modify
      ( \mv ->
          MV.unsafeModify mv (unsafeCoerce . f . unsafeCoerce) (fromIntegral $ natVal k)
      )
      vec

hfoldr ::
  forall h as b.
  ( forall k x.
    ( KnownNat k
    , Member (h x) (Map h as)
    , Member x as
    , ElemAt k as ~ x
    ) =>
    Proxy k ->
    Proxy x ->
    h x ->
    b ->
    b
  ) ->
  b ->
  HList h as ->
  b
{-# INLINE hfoldr #-}
hfoldr f = \z0 hl ->
  appEndo (hfoldMap (\p px x -> Endo (f p px x)) hl) z0

hfoldl' ::
  forall h as b.
  ( forall k x.
    ( KnownNat k
    , Member (h x) (Map h as)
    , Member x as
    , ElemAt k as ~ x
    ) =>
    Proxy k ->
    Proxy x ->
    b ->
    h x ->
    b
  ) ->
  b ->
  HList h as ->
  b
{-# INLINE hfoldl' #-}
hfoldl' f = flip $ hfoldr (\l n x k z -> k $! f l n z x) id

hfoldMap ::
  forall h as w.
  (Monoid w) =>
  ( forall k x.
    ( KnownNat k
    , ElemAt k as ~ x
    , Member (h x) (Map h as)
    , Member x as
    ) =>
    Proxy k ->
    Proxy x ->
    h x ->
    w
  ) ->
  HList h as ->
  w
hfoldMap f (HL v) =
  flip foldMap (V.indexed v) $ \(fromIntegral -> k, a) ->
    withKnownNat k $ \p@(Proxy :: Proxy k) ->
      f p (Proxy :: Proxy (ElemAt k as)) (unsafeCoerce a)

htraverse ::
  forall g bs f h as.
  (Applicative f) =>
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (h (ElemAt k as)) (Map h as)
    ) =>
    Proxy k ->
    h (ElemAt k as) ->
    f (g (ElemAt k bs))
  ) ->
  HList h as ->
  f (HList g bs)
htraverse f (HL v) =
  HL
    <$> flip
      traverse
      (V.indexed v)
      ( \(fromIntegral -> k, a) ->
          withKnownNat k $ \p@(Proxy :: Proxy k) ->
            unsafeCoerce @_ @Any <$> f p (unsafeCoerce a)
      )

htraverse_ ::
  forall f h as.
  (Applicative f) =>
  ( forall k.
    ( KnownNat k
    , Member (ElemAt k as) as
    , Member (h (ElemAt k as)) (Map h as)
    ) =>
    Proxy k ->
    h (ElemAt k as) ->
    f ()
  ) ->
  HList h as ->
  f ()
htraverse_ f (HL v) =
  flip
    F.traverse_
    (V.indexed v)
    ( \(fromIntegral -> k, a) ->
        withKnownNat k $ \p@(Proxy :: Proxy k) ->
          f p (unsafeCoerce a :: h (ElemAt k as))
    )

hunzip ::
  forall h as bs.
  HList h (ZipSame as bs) ->
  (HList h as, HList h bs)
hunzip (HL v) =
  let (l, r) =
        V.unzip $
          V.imap
            ( \k ->
                withKnownNat (fromIntegral k) $ \(Proxy :: Proxy k) ->
                  (unsafeCoerce *** unsafeCoerce)
                    . unsafeCoerce @Any @(ElemAt k as, ElemAt k bs)
            )
            v
   in (HL l, HL r)

hunzip' ::
  forall h g as.
  HList (Product h g) as ->
  (HList h as, HList g as)
hunzip' (HL v) =
  let (l, r) =
        V.unzip $
          V.imap
            ( \k ->
                withKnownNat (fromIntegral k) $ \(Proxy :: Proxy k) ->
                  (\(Pair x y) -> (unsafeCoerce x, unsafeCoerce y))
                    . unsafeCoerce @Any @(Product h g (ElemAt k as))
            )
            v
   in (HL l, HL r)

hunzipWith ::
  forall h as g k.
  (forall x. (Member x as, Member (h x) (Map h as)) => h x -> (g x, k x)) ->
  HList h as ->
  (HList g as, HList k as)
hunzipWith f (HL v) =
  (HL *** HL) $
    V.unzip $
      V.imap
        ( \(fromIntegral -> k) hx -> withKnownNat k $ \(Proxy :: Proxy n) ->
            (unsafeCoerce *** unsafeCoerce) $
              f (unsafeCoerce @_ @(h (ElemAt n as)) hx)
        )
        v

hunzipWithM ::
  forall h as g k m.
  (Monad m) =>
  ( forall n.
    ( KnownNat n
    , Member (ElemAt n as) as
    , Member (ElemAt n as) as
    , Member (h (ElemAt n as)) (Map h as)
    , Member (g (ElemAt n as)) (Map g as)
    , Member (k (ElemAt n as)) (Map k as)
    ) =>
    Proxy n ->
    h (ElemAt n as) ->
    m (g (ElemAt n as), k (ElemAt n as))
  ) ->
  HList h as ->
  m (HList g as, HList k as)
hunzipWithM f (HL v) =
  (HL *** HL) . V.unzip
    <$> V.imapM
      ( \(fromIntegral -> k) hx -> withKnownNat k $ \p@(Proxy :: Proxy n) ->
          (unsafeCoerce *** unsafeCoerce)
            <$> f p (unsafeCoerce @_ @(h (ElemAt n as)) hx)
      )
      v
