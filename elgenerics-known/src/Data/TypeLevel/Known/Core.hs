{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.TypeLevel.Known.Core (
  Sing,
  SNat,
  SSymbol,
  knownSymbolVal,
  knownNatVal,
  STestEquality (..),
  sTestTypeableEquality,
  Equality (..),
  WrapSing (..),
  STuple (..),
  STriple (..),
  SList (..),
  SUnit (..),
  SVoid (),
  Known (..),
  ShowSing (),
  ShowSing' (),
  withKnown,
  withKnown',
  knownVal#,
  knownVal,
  knownVal',
  sKnownVal#,
  sKnownVal,
  withKnownNat',
  toKnownNat,
  withKnownSymbol',
  toKnownSymbol,
  SomeTypeRep' (..),
  SomeSing (..),
  HasSing (..),
  SingTypeable (..),
  withSingTypeable,
  type (===),
  SApply (..),
  Snd,
  Snd1,
  Fst,
  Fst1,
  First,
  First2,
  First1,
  Second,
  Second2,
  Second1,
  Uncurry,
  Swap,
  Swap1,
) where

import Data.Kind (Type)
import Data.Proxy
import Data.Type.Equality (TestEquality (..), gcastWith, type (==))
import Data.TypeLevel.Function
import Data.Void (Void)
import GHC.Exts
import GHC.TypeLits (KnownSymbol, SomeSymbol (..), Symbol, someSymbolVal, symbolVal')
import GHC.TypeNats (KnownNat, Nat, SomeNat (SomeNat), natVal', someNatVal)
import Numeric.Natural (Natural)
import Type.Reflection
import Type.Reflection.Unsafe (typeRepFingerprint)
import Unsafe.Coerce (unsafeCoerce)

type family Sing :: k -> Type

data SomeSing k where
  MkSomeSing :: Sing (a :: k) -> SomeSing k

instance (ShowSing k) => Show (SomeSing k) where
  showsPrec d (MkSomeSing sng) =
    showParen (d > 10) $
      showString "MkSomeSing " . showsPrec 11 sng

newtype WithKnown a r = WithKnown ((Known a) => r)

withKnown' :: forall a r. Sing a -> ((Known a) => r) -> r
withKnown' s act =
  unsafeCoerce (WithKnown @a @r act) s

withKnown ::
  forall a r. Sing a -> ((Known a) => Proxy a -> r) -> r
withKnown s act = withKnown' @a @(Proxy a -> r) s act Proxy

class HasSing k where
  type Demote k :: Type
  type Demote k = k
  demote :: Sing (a :: k) -> Demote k
  promote :: Demote k -> SomeSing k

class (Typeable k) => SingTypeable k where
  singTypeRep :: Sing (x :: k) -> TypeRep x

withSingTypeable ::
  (SingTypeable k) => Sing (x :: k) -> ((Typeable x) => r) -> r
{-# INLINE withSingTypeable #-}
withSingTypeable sing = withTypeable (singTypeRep sing)

{- | A type @a@ whose singleton is known statically (corresponds to 'SingI' in @singletons@).
 c.f. 'sKnownVal', 'sKnownVal#', 'withKnown', and 'withKnown''
-}
class Known a where
  sKnownVal' :: Sing a

sKnownVal# :: (Known a) => Proxy# a -> Sing a
sKnownVal# (_ :: Proxy# a) = sKnownVal' @a

sKnownVal :: (Known a) => pxy a -> Sing a
sKnownVal (_ :: pxy a) = sKnownVal' @a

knownVal# ::
  forall {k} (a :: k).
  (Known (a :: k), HasSing k) =>
  Proxy# a ->
  Demote k
knownVal# _ = demote @k $ sKnownVal' @a

knownVal' ::
  forall {k} (a :: k).
  (Known a, HasSing k) =>
  Demote k
knownVal' = demote @k $ sKnownVal' @a

knownVal ::
  forall {k} (a :: k) pxy.
  (Known a, HasSing k) =>
  pxy a ->
  Demote k
knownVal = const $ knownVal' @a

data Equality a b where
  Equal :: (a ~ b, (a == b) ~ 'True, (a === b) ~ 'True) => Equality a b
  NonEqual :: ((a === b) ~ 'False, (a == b) ~ 'False) => Equality a b

deriving instance Show (Equality a b)

class STestEquality k where
  sTestEquality :: Sing (a :: k) -> Sing b -> Equality a b

newtype SNat (n :: Nat) = SNat {unSNat :: Natural}
  deriving (Eq, Ord)

instance Show (SNat n) where
  showsPrec d (SNat n) = showsPrec d n

knownNatVal :: SNat n -> Natural
{-# INLINE knownNatVal #-}
knownNatVal = unSNat

type instance Sing = SNat

instance SingTypeable Nat where
  singTypeRep sn = withKnownNat' sn typeRep
  {-# INLINE singTypeRep #-}

instance HasSing Nat where
  type Demote Nat = Natural
  demote = coerce
  promote = MkSomeSing . coerce

deriving via
  WrapSing
  instance
    TestEquality SNat

instance STestEquality Nat where
  {-# INLINE sTestEquality #-}
  sTestEquality = \(SNat l) (SNat r) ->
    if l == r
      then unsafeCoerce $ Equal @() @()
      else unsafeCoerce $ NonEqual @1 @2

instance (KnownNat n) => Known n where
  sKnownVal' = SNat $ natVal' @n proxy#

toKnownNat :: forall n r. (Known n) => ((KnownNat n) => r) -> r
toKnownNat act =
  case someNatVal $ unSNat $ sKnownVal' @n of
    SomeNat (_ :: Proxy n') ->
      gcastWith (unsafeCoerce $ Refl @() :: n :~: n') act

withKnownNat' ::
  SNat n ->
  ((Known n, KnownNat n) => r) ->
  r
{-# INLINE withKnownNat' #-}
withKnownNat' (sn :: SNat n) = \a -> withKnown' sn $ toKnownNat @n a

newtype SSymbol (s :: Symbol) = SSymbol {unSSymbol :: String}
  deriving (Eq, Ord)

instance Show (SSymbol sym) where
  showsPrec d = showsPrec d . unSSymbol

type instance Sing = SSymbol

knownSymbolVal :: SSymbol n -> String
{-# INLINE knownSymbolVal #-}
knownSymbolVal = unSSymbol

withKnownSymbol' ::
  forall sym r. SSymbol sym -> ((Known sym, KnownSymbol sym) => r) -> r
{-# INLINE withKnownSymbol' #-}
withKnownSymbol' ssym = \a -> withKnown' ssym $ toKnownSymbol @sym a

toKnownSymbol ::
  forall sym r.
  (Known sym) =>
  ((KnownSymbol sym) => r) ->
  r
toKnownSymbol act =
  case someSymbolVal $ unSSymbol $ sKnownVal' @sym of
    SomeSymbol (_ :: Proxy sym') ->
      gcastWith (unsafeCoerce (Refl @()) :: sym :~: sym') act

instance (KnownSymbol s) => Known s where
  sKnownVal' = SSymbol $ symbolVal' @s proxy#

instance HasSing Symbol where
  type Demote Symbol = String
  demote = unSSymbol
  promote = MkSomeSing . SSymbol

instance SingTypeable Symbol where
  singTypeRep ssym = withKnownSymbol' ssym typeRep
  {-# INLINE singTypeRep #-}

deriving via
  WrapSing
  instance
    TestEquality SSymbol

instance STestEquality Symbol where
  {-# INLINE sTestEquality #-}
  sTestEquality = \(SSymbol l) (SSymbol r) ->
    if l == r
      then unsafeCoerce $ Equal @() @()
      else unsafeCoerce $ NonEqual @"" @"x"

newtype WrapSing a = WrapSing {unwrapSing :: Sing a}

deriving newtype instance (Show (Sing a)) => Show (WrapSing a)

instance (STestEquality k) => TestEquality (WrapSing :: k -> Type) where
  {-# INLINE testEquality #-}
  testEquality = \(WrapSing l) (WrapSing r) ->
    case sTestEquality l r of
      Equal -> Just Refl
      _ -> Nothing

sTestTypeableEquality ::
  forall a b.
  (Typeable a, Typeable b) =>
  Equality a b
{-# INLINE sTestTypeableEquality #-}
sTestTypeableEquality =
  case testEquality (typeRep @a) (typeRep @b) of
    Just Refl -> unsafeCoerce $ Equal @()
    Nothing -> unsafeCoerce $ NonEqual @1 @2

data STuple (tpl :: (a, b)) where
  SPair :: Sing a -> Sing b -> STuple '(a, b)

deriving instance (ShowSing a, ShowSing b) => Show (STuple (tpl :: (a, b)))

type instance Sing = STuple

instance (Known a, Known b) => Known '(a, b) where
  sKnownVal' = SPair sKnownVal' sKnownVal'

instance
  (SingTypeable a, SingTypeable b) =>
  SingTypeable (a, b)
  where
  {-# INLINE singTypeRep #-}
  singTypeRep (SPair l r) =
    withSingTypeable l $ withSingTypeable r typeRep

instance (HasSing a, HasSing b) => HasSing (a, b) where
  type Demote (a, b) = (Demote a, Demote b)
  demote = \case
    SPair a b -> (demote a, demote b)
  promote = \(a, b) ->
    case (promote a, promote b) of
      (MkSomeSing l, MkSomeSing r) -> MkSomeSing $ SPair l r

instance
  (STestEquality a, STestEquality b) =>
  STestEquality (a, b)
  where
  {-# INLINE sTestEquality #-}
  sTestEquality = \(SPair a b) (SPair a' b') ->
    case (sTestEquality a a', sTestEquality b b') of
      (Equal, Equal) -> Equal
      (NonEqual, _) -> unsafeCoerce $ NonEqual @0 @1
      (_, NonEqual) -> unsafeCoerce $ NonEqual @0 @1

deriving via
  WrapSing
  instance
    (STestEquality a, STestEquality b) =>
    TestEquality (STuple :: (a, b) -> Type)

data STriple (tpl :: (a, b, c)) where
  SMkTriple :: Sing a -> Sing b -> Sing c -> STriple '(a, b, c)

deriving instance
  (ShowSing a, ShowSing b, ShowSing c) =>
  Show (STriple (tpl :: (a, b, c)))

type instance Sing = STriple

instance (Known a, Known b, Known c) => Known '(a, b, c) where
  sKnownVal' = SMkTriple sKnownVal' sKnownVal' sKnownVal'

instance (SingTypeable a, SingTypeable b, SingTypeable c) => SingTypeable (a, b, c) where
  {-# INLINE singTypeRep #-}
  singTypeRep (SMkTriple a b c) =
    withSingTypeable a $
      withSingTypeable b $
        withSingTypeable c typeRep

instance (HasSing a, HasSing b, HasSing c) => HasSing (a, b, c) where
  type Demote (a, b, c) = (Demote a, Demote b, Demote c)
  demote = \case
    SMkTriple a b c -> (demote a, demote b, demote c)
  promote = \(a, b, c) ->
    case (promote a, promote b, promote c) of
      (MkSomeSing l, MkSomeSing r, MkSomeSing u) ->
        MkSomeSing $ SMkTriple l r u

instance
  (STestEquality a, STestEquality b, STestEquality c) =>
  STestEquality (a, b, c)
  where
  {-# INLINE sTestEquality #-}
  sTestEquality = \(SMkTriple a b c) (SMkTriple a' b' c') ->
    case (sTestEquality a a', sTestEquality b b', sTestEquality c c') of
      (Equal, Equal, Equal) -> Equal
      (NonEqual, _, _) -> unsafeCoerce $ NonEqual @0 @1
      (_, NonEqual, _) -> unsafeCoerce $ NonEqual @0 @1
      (_, _, NonEqual) -> unsafeCoerce $ NonEqual @0 @1

deriving via
  WrapSing
  instance
    (STestEquality a, STestEquality b, STestEquality c) =>
    TestEquality (STriple :: (a, b, c) -> Type)

data SomeTypeRep' where
  MkSomeTypeRep' :: TypeRep (a :: Type) -> SomeTypeRep'

deriving instance Show SomeTypeRep'

type instance Sing = (TypeRep :: Type -> Type)

instance SingTypeable Type where
  singTypeRep = id
  {-# INLINE singTypeRep #-}

instance HasSing Type where
  type Demote Type = SomeTypeRep'
  demote = MkSomeTypeRep'
  promote = \case
    MkSomeTypeRep' (rep :: TypeRep a) -> MkSomeSing rep

instance (Typeable (a :: Type), (a === a) ~ 'True) => Known a where
  sKnownVal' = typeRep
  {-# INLINE sKnownVal' #-}

instance STestEquality Type where
  {-# INLINE sTestEquality #-}
  sTestEquality = \l r ->
    if typeRepFingerprint l == typeRepFingerprint r
      then unsafeCoerce $ Equal @0
      else unsafeCoerce $ NonEqual @0 @1

data SList (xs :: [k]) where
  SNil :: SList '[]
  (:%) :: Sing x -> SList xs -> SList (x ': xs)

infixr 8 :%

instance (ShowSing k) => Show (SList (lst :: [k])) where
  showsPrec _ s = showChar '[' . go s . showChar ']'
    where
      go :: SList (xs :: [k]) -> ShowS
      go SNil = id
      go (sx :% SNil) = shows sx
      go (sx :% sxs) = shows sx . showString ", " . go sxs

type instance Sing = SList

deriving instance Typeable SList

instance (SingTypeable a) => SingTypeable [a] where
  {-# INLINE singTypeRep #-}
  singTypeRep = go
    where
      go :: SList (xs :: [a]) -> TypeRep xs
      go SNil = typeRep
      go (sx :% xs) =
        withSingTypeable sx $ withTypeable (go xs) typeRep

instance Known ('[] :: [k]) where
  sKnownVal' = SNil
  {-# INLINE sKnownVal' #-}

instance (Known x, Known xs) => Known (x ': xs) where
  sKnownVal' = sKnownVal' :% sKnownVal'
  {-# INLINE sKnownVal' #-}

instance (HasSing k) => HasSing [k] where
  type Demote [k] = [Demote k]
  demote = \case
    SNil -> []
    l :% xs -> demote l : demote xs
  {-# INLINE demote #-}
  promote = \case
    [] -> MkSomeSing SNil
    (x : xs)
      | MkSomeSing sx <- promote x
      , MkSomeSing sxs <- promote xs ->
          MkSomeSing $ sx :% sxs
  {-# INLINE promote #-}

instance (STestEquality k) => STestEquality [k] where
  {-# INLINE sTestEquality #-}
  sTestEquality = \l r -> case (l, r) of
    (SNil, SNil) -> Equal
    (a :% as, b :% bs)
      | Equal <- sTestEquality a b
      , Equal <- sTestEquality as bs ->
          Equal
    _ -> unsafeCoerce $ NonEqual @Int @Bool

deriving via
  WrapSing
  instance
    (STestEquality k) =>
    TestEquality (SList :: [k] -> Type)

{-
-- Sing and Skeleton can be unified using the
-- following HKD-like construction:

type family SkeletonF (l :: forall k. k -> Type) (self :: a -> Type) (x :: a)
  = r | r -> x
type Sing =
  SkeletonF WrapSing WrapSing
            -- Sing cannot be here b/c it is a (non-saturated) type family!
-}

data SUnit (a :: ()) where
  SUnit :: SUnit '()

deriving instance Show (SUnit unit)

type instance Sing = SUnit

instance SingTypeable () where
  singTypeRep SUnit = typeRep
  {-# INLINE singTypeRep #-}

instance Known '() where
  sKnownVal' = SUnit
  {-# INLINE sKnownVal' #-}

instance HasSing () where
  demote = const ()
  {-# INLINE demote #-}
  promote = const $ MkSomeSing SUnit
  {-# INLINE promote #-}

instance STestEquality () where
  sTestEquality SUnit SUnit = Equal
  {-# INLINE sTestEquality #-}

deriving via WrapSing instance TestEquality SUnit

infix 4 ===

{- | A variant of '(Data.Type.Equality.==)' that takes
   only reflexivity into account and stop bothering with
   injectivity concerns.
-}
type family (===) (a :: k) (b :: k) :: Bool where
  a === a = 'True
  a === b = 'False

data SVoid (void :: Void) deriving (Show)

type instance Sing = SVoid

instance HasSing Void where
  promote = \case {}
  demote = \case {}

instance STestEquality Void where
  sTestEquality = \case {}

instance SingTypeable Void where
  singTypeRep = \case {}

deriving via
  WrapSing
  instance
    TestEquality (SVoid :: Void -> Type)

class (forall (z :: k). ShowSing' z) => ShowSing (k :: Type)

instance (forall (z :: k). ShowSing' z) => ShowSing (k :: Type)

class (forall sing. (sing ~ Sing) => Show (sing z)) => ShowSing' z

instance (Show (Sing z)) => ShowSing' z

type SApply :: forall k k'. (k ~> k') -> Constraint
class SApply (f :: k ~> k') where
  sApply :: Proxy# f -> Sing (a :: k) -> Sing (Apply f a :: k')

-- >>> :t sApply
-- sApply
--   :: forall k k' (f :: k ~> k') (a :: k).
--      SApply f =>
--      Proxy# f -> Sing a -> Sing (Apply f a)

type family Snd (p :: (a, b)) :: b where
  Snd '(_, b) = b

type family Fst (p :: (a, b)) :: a where
  Fst '(a, _) = a

data Snd1 :: (a, b) ~> b

type instance Apply Snd1 p = Snd p

data Fst1 :: (a, b) ~> a

type instance Apply Fst1 p = Fst p

type family First (f :: a ~> a') (pr :: (a, b)) :: (a', b) where
  First f '(a, b) = '(Apply f a, b)

type family Second (f :: b ~> b') (pr :: (a, b)) :: (a, b') where
  Second f '(a, b) = '(a, Apply f b)

data First2 :: (a ~> a') ~> (a, b) ~> (a', b)

data First1 (f :: a ~> a') :: (a, b) ~> (a', b)

data Second2 :: (b ~> b') ~> (a, b) ~> (a, b')

data Second1 (f :: b ~> b') :: (a, b) ~> (a, b')

type instance Apply First2 f = First1 f

type instance Apply (First1 f) p = First f p

type instance Apply Second2 f = Second1 f

type instance Apply (Second1 f) p = Second f p

data Uncurry (a :: b -> c -> d) :: (b, c) ~> d

type instance Apply (Uncurry f) tpl = f (Fst tpl) (Snd tpl)

type family Swap (tpl :: (a, b)) :: (b, a) where
  Swap '(a, b) = '(b, a)

data Swap1 :: (a, b) ~> (b, a)

type instance Apply Swap1 tpl = Swap tpl

instance SApply (Fst1 :: (k, k') ~> k) where
  sApply _ (SPair l _) = l

instance SApply (Snd1 :: (k, k') ~> k') where
  sApply _ (SPair _ r) = r

instance SApply (Swap1 :: (k, k') ~> (k', k)) where
  sApply _ (SPair l r) = SPair r l
