{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.List.Solver #-}

-- | エントリーにだけ依存するレコードのインタフェース
module Data.Record.HigherKinded.OnEntry (
  Record,
  HasLabel,
  OnEntry (..),
  IsRecord (..),
  Labels,
  Entries,
  field,
  type (<:),
  (:=) (..),
  FieldLabel (..),
  traverseRec,
  traverseRecC,
  traverseRec_,
  traverseRecC_,
  foldMapRec,
  foldMapRecC,
  singletonRec,
  singletonRec',
  emptyRec,
  (&.),
  Extendible,
  (&+),
  Modifiable,
  (&%~),
  (&|~),
  (&-),
  generateRec,
  generateRecM,
  fields,
) where

import Data.Coerce
import Data.Functor.Const
import Data.Proxy
import Data.Record.HigherKinded (
  Extendible,
  FieldLabel (..),
  HasLabel,
  IsRecord (..),
  Modifiable,
  OnEntry (..),
  field,
  (:=) (..),
  type (<:),
 )
import Data.Record.HigherKinded qualified as HK
import Data.TypeLevel.OrdMap
import GHC.TypeLits

type Record h = HK.Record (HK.OnEntry h)

emptyRec :: Record h Empty
emptyRec = HK.emptyRec

singletonRec ::
  h a -> Record h (Singleton l a)
singletonRec = HK.singletonRec . OnEntry

singletonRec' ::
  l := h a ->
  Record h (Singleton l a)
singletonRec' = HK.singletonRec' . coerce

fields ::
  forall a.
  ( IsRecord a
  , AllOM (HK.LabelC KnownSymbol) (Fields a)
  ) =>
  Record (Const String) (Fields a)
fields = HK.fields @a

traverseRec ::
  forall f h g as.
  (Applicative f) =>
  ( forall l x n.
    (LookupWithIndex l as ~ 'Just '(x, n), KnownNat n) =>
    Proxy l ->
    Proxy x ->
    Proxy n ->
    h x ->
    f (g x)
  ) ->
  Record h as ->
  f (Record g as)
{-# INLINE traverseRec #-}
traverseRec = \f -> HK.traverseRec $ \l x n (OnEntry hx) ->
  OnEntry <$> f l x n hx

traverseRecC ::
  forall c f h g as.
  (Applicative f, AllOM (EntryC c) as) =>
  ( forall l x n.
    (LookupWithIndex l as ~ 'Just '(x, n), KnownNat n, c x) =>
    Proxy l ->
    Proxy x ->
    Proxy n ->
    h x ->
    f (g x)
  ) ->
  Record h as ->
  f (Record g as)
{-# INLINE traverseRecC #-}
traverseRecC f =
  traverseRec $
    \(l :: Proxy l)
     (x :: Proxy x)
     (n :: Proxy n)
     (hx :: h x) -> f l x n hx

traverseRec_ ::
  forall f h as.
  (Applicative f) =>
  ( forall l x n.
    (LookupWithIndex l as ~ 'Just '(x, n), KnownNat n) =>
    Proxy l ->
    Proxy x ->
    Proxy n ->
    h x ->
    f ()
  ) ->
  Record h as ->
  f ()
{-# INLINE traverseRec_ #-}
traverseRec_ = \f -> HK.traverseRec_ $ \l x n ->
  f l x n . runOnEntry

traverseRecC_ ::
  forall c f h as.
  (Applicative f, AllOM (EntryC c) as) =>
  ( forall l x n.
    (LookupWithIndex l as ~ 'Just '(x, n), KnownNat n, c x) =>
    Proxy l ->
    Proxy x ->
    Proxy n ->
    h x ->
    f ()
  ) ->
  Record h as ->
  f ()
{-# INLINE traverseRecC_ #-}
traverseRecC_ = \f -> HK.traverseRecC_ @(EntryC c) @f @(OnEntry h) @as $
  \l x n (OnEntry hx) ->
    f l x n hx

foldMapRec ::
  forall h fs w.
  (Monoid w) =>
  ( forall l v n.
    (LookupWithIndex l fs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h v ->
    w
  ) ->
  Record h fs ->
  w
{-# INLINE foldMapRec #-}
foldMapRec = \f ->
  HK.foldMapRec $ \(l :: Proxy l) v n ->
    f l v n . runOnEntry

foldMapRecC ::
  forall c h fs w.
  (Monoid w, AllOM (EntryC c) fs) =>
  ( forall l v n.
    (LookupWithIndex l fs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h v ->
    w
  ) ->
  Record h fs ->
  w
{-# INLINE foldMapRecC #-}
foldMapRecC = \f -> foldMapRec f

(&.) ::
  forall l xs h.
  (HasLabel l xs) =>
  Record h xs ->
  l := h (Lookup' l xs) ->
  Record h xs
(&.) = \r -> (HK.&.) r . fmap OnEntry

infixl 1 &.

(&+) ::
  forall l x xs h.
  (Extendible (l ::: x) xs) =>
  Record h xs ->
  l := h x ->
  Record h ((l ::: x) <: xs)
(&+) = coerce $ (HK.&+) @l @x @xs @(OnEntry h)

infixl 1 &+

(&%~) ::
  forall l xs h a.
  (Modifiable l a xs) =>
  Record h xs ->
  l := (h (Lookup' l xs) -> h a) ->
  Record h ((l ::: a) <: xs)
(&%~) = coerce $ (HK.&%~) @l @xs @(OnEntry h) @a

infixl 1 &%~

(&|~) ::
  forall l xs a h.
  (HasLabel l xs) =>
  Record h xs ->
  l := h a ->
  Record h ((l ::: a) <: xs)
(&|~) = coerce $ (HK.&|~) @l @xs @a @(OnEntry h)

infixl 1 &|~

(&-) ::
  forall l xs h.
  (HasLabel l xs) =>
  Record h xs ->
  FieldLabel l ->
  Record h (Delete l xs)
(&-) = (HK.&-)

infixl 1 &-

generateRec ::
  forall recs h.
  (KnownNat (Size recs)) =>
  ( forall l v n.
    (LookupWithIndex l recs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    h v
  ) ->
  Record h recs
{-# INLINE generateRec #-}
generateRec = \f -> HK.generateRec $ \a b -> OnEntry . f a b

generateRecM ::
  forall recs h m.
  ( KnownNat (Size recs)
  , Monad m
  ) =>
  ( forall l v n.
    (LookupWithIndex l recs ~ 'Just '(v, n), KnownNat n) =>
    Proxy l ->
    Proxy v ->
    Proxy n ->
    m (h v)
  ) ->
  m (Record h recs)
{-# INLINE generateRecM #-}
generateRecM = \f -> HK.generateRecM $ \a b -> fmap OnEntry . f a b
