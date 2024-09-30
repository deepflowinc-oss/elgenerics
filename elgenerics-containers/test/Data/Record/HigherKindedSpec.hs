{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Wno-orphans -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -fplugin Data.Record.Plugin #-}
{-# OPTIONS_GHC -fplugin Data.TypeLevel.List.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
{-# OPTIONS_GHC -fplugin-opt Data.Record.Plugin:MyRecord #-}
{-# OPTIONS_GHC -fplugin-opt GHC.TypeLits.Presburger:allow-negated-numbers #-}

module Data.Record.HigherKindedSpec where

import Control.DeepSeq (NFData, force)
import Control.Exception (
  TypeError (TypeError),
  evaluate,
  try,
 )
import Control.Lens (Identity, (&), (.~), (^.), (^?))
import Data.Kind
import Data.Proxy
import Data.Record.Cases
import Data.Record.Failures (
  mismatchUpdate,
  typeMismatch,
  unmergeable,
 )
import Data.Record.HigherKinded
import Data.Record.HigherKinded qualified as HK
import Data.Tagged
import Data.Text qualified as T
import Data.TypeLevel.Known
import Data.TypeLevel.Nat
import Data.Vector qualified as V
import Data.Void (Void)
import GHC.Generics
import GHC.TypeLits (Symbol)
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Type.Reflection

data Test1 = Test1
  { foo :: Integer
  , bar :: Bool
  , buz :: Maybe String
  , quux :: Either Ordering Int
  , dablin :: V.Vector Double
  }
  deriving (Generic, Typeable, Eq, Show, Ord)
  deriving anyclass (IsRecord, IsHRecord STagged)

goldenTest1_raw :: Test1
goldenTest1_raw =
  Test1
    { foo = (12 :: Integer)
    , bar = True
    , buz = Just "dear"
    , quux = Left LT
    , dablin = V.replicate 50 pi
    }

goldenTest1_extrec :: Record STagged (Fields Test1)
goldenTest1_extrec = toRecord $ goldenTest1_raw

proxyType :: a -> Proxy a
proxyType = const Proxy

instance Arbitrary Test1 where
  arbitrary =
    Test1
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> (V.fromList <$> arbitrary)

deriving newtype instance (Arbitrary a) => Arbitrary (Tagged s a)

instance
  (AllOM (OverC h Arbitrary) dic) =>
  Arbitrary (Record h dic)
  where
  arbitrary =
    generateRecM $ \(_ :: Proxy l) (_ :: Proxy v) _ ->
      arbitrary @(h l v)

type TypeLabelledFields =
  FromList
    '[ String ::: 2
     , Int ::: 4
     , Maybe Bool ::: 3
     , () ::: 0
     , Ordering ::: 5
     ]

data Vec a n where
  VNil :: Vec a 0
  (:<) :: a -> Vec a n -> Vec a (1 + n)

infixr 9 :<

deriving instance Typeable Vec

deriving instance (Show a) => Show (Vec a n)

deriving instance (Eq a) => Eq (Vec a n)

tyLabRec :: Record Vec TypeLabelledFields
tyLabRec = castRecord tyLabRec'

type Zero = 0

type RawTypeFields =
  ( (Ordering ::: 5)
      <: (Maybe Bool ::: 3)
      <: (Int ::: 4)
      <: (String ::: 2)
      <: Singleton () 0
  )

fiveOrderings :: Vec Ordering 5
fiveOrderings = GT :< EQ :< LT :< EQ :< GT :< VNil

type FiveOrds = Vec Ordering 5

tyLabRec' :: Record Vec RawTypeFields
tyLabRec' =
  singletonRec (VNil @())
    &+ field @String
    := ("foo" :< "buz" :< VNil)
    &+ field @Int
    := (42 :< 5 :< 9 :< (-3) :< VNil)
    &+ field @(Maybe Bool)
    := (Just True :< Nothing :< Just False :< VNil)
    &+ field @Ordering
    := fiveOrderings

tyLabRecSimple :: Record Proxy2 RawTypeFields
tyLabRecSimple =
  singletonRec (Proxy2 @() @0)
    &+ field @String
    := Proxy2
    &+ field @Int
    := Proxy2
    &+ field @(Maybe Bool)
    := Proxy2
    &+ field @Ordering
    := Proxy2

type VecRep a n =
  D1
    ('MetaData "Vec" "Data.Record.HigherKindedSpec" "elgenerics" 'False)
    ( C1
        ('MetaCons "MkVec" 'PrefixI 'False)
        (VecRepAuxN (n === 0) (n === 1) a n)
    )

type NoLab =
  S1 ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)

type family VecRepAuxN is0 is1 a n :: Type -> Type where
  VecRepAuxN 'True _ _a 0 = U1
  VecRepAuxN 'False 'True a 1 = NoLab (Rec0 a)
  VecRepAuxN 'False 'False a n =
    NoLab (Rec0 a)
      :*: VecRepAuxN ((n - 1) === 0) ((n - 1) === 1) a (n - 1)

data Proxy2 a b = Proxy2
  deriving (Read, Show, Eq, Ord, Typeable, Generic)

toVecRepAux ::
  forall a n x.
  (KnownNat n) =>
  Vec a n ->
  VecRepAuxN (n === 0) (n === 1) a n x
toVecRepAux =
  case sTestEquality sn (sKnownVal' @0) of
    Equal -> const U1
    NonEqual ->
      case sTestEquality sn (sKnownVal' @1) of
        Equal -> \case
          (a :< VNil) -> M1 $ K1 a
          (_ :< _ :< _) -> error "impossible"
        NonEqual -> \case
          (a :< as) ->
            M1 (K1 a) :*: toVecRepAux @a @(n - 1) as
  where
    sn = sKnownVal' @n

fromVecRepAux :: forall a n x. (KnownNat n) => VecRepAuxN (n === 0) (n === 1) a n x -> Vec a n
fromVecRepAux =
  case sTestEquality sn (sKnownVal' @0) of
    Equal -> const VNil
    NonEqual ->
      case sTestEquality sn (sKnownVal' @1) of
        Equal -> \case
          M1 (K1 x) -> x :< VNil
        NonEqual -> \case
          (M1 (K1 a) :*: r) ->
            withKnownNat' (sn %- sKnownVal' @1) $
              a :< fromVecRepAux @a @(n - 1) r
  where
    sn = sKnownVal' @n

type ThreeBools = Vec Bool 3

instance (KnownNat n) => Generic (Vec a n) where
  type Rep (Vec a n) = VecRep a n
  from = M1 . M1 . toVecRepAux
  to = fromVecRepAux . unM1 . unM1

generateVecA ::
  forall f a n.
  (Applicative f, KnownNat n) =>
  (Int -> f a) ->
  f (Vec a n)
generateVecA fa = go (sKnownVal' @0)
  where
    sn = sKnownVal' @n
    go :: forall m. SNat m -> f (Vec a (n - m))
    go sm = withKnownNat' sm $
      case sTestEquality sm sn of
        Equal -> pure VNil
        NonEqual ->
          (:<)
            <$> fa (fromIntegral $ natVal sm)
            <*> go (sm %+ sKnownVal' @1)

replicateVecA :: forall f a n. (Applicative f, KnownNat n) => f a -> f (Vec a n)
replicateVecA fa = go (sKnownVal' @0)
  where
    sn = sKnownVal' @n
    go :: forall m. SNat m -> f (Vec a (n - m))
    go sm =
      case sTestEquality sm sn of
        Equal -> pure VNil
        NonEqual -> (:<) <$> fa <*> withKnownNat' sm (go $ sm %+ sKnownVal' @1)

replicateVec' :: forall a n. (KnownNat n) => a -> Vec a n
replicateVec' a = go (sKnownVal' @n)
  where
    go :: forall m. SNat m -> Vec a m
    go sm =
      case sTestEquality sm (sKnownVal' @0) of
        Equal -> VNil
        NonEqual -> a :< withKnownNat' sm (go $ sm %- sKnownVal' @1)

instance (KnownNat n, Arbitrary a) => Arbitrary (Vec a n) where
  arbitrary = replicateVecA arbitrary

instance (Arbitrary a) => Arbitrary (V.Vector a) where
  arbitrary = V.fromList <$> arbitrary

test_generics :: TestTree
test_generics =
  testGroup
    "Generics"
    [ testGroup
        "to . from == id"
        [ testProperty "Fields Test1" $ \rec1 ->
            to (from (rec1 :: Record STagged (Fields Test1)))
              === rec1
        , testProperty "Record Vec TypeLablledFields" $ \rec1 ->
            to (from (rec1 :: Record Vec TypeLabelledFields))
              === rec1
        , testProperty "Record Vec RawTypeFields" $ \rec1 ->
            to (from (rec1 :: Record Vec RawTypeFields))
              === rec1
        ]
    ]

test_symbol_rec :: TestTree
test_symbol_rec =
  testGroup
    "Symbol-labelled rank-1 record"
    [ testProperty "fromRecord . toRecord == id" $
        \t1@Test1 {} ->
          fromRecord (toRecord t1) == t1
    , testProperty "toRecord . fromRecord == castRecord" $
        \rec1 ->
          toRecord (fromRecord @Test1 @(Fields Test1) rec1) == castRecord rec1
    , testProperty "fromHRecord . toHRecord == id" $
        \t1@Test1 {} ->
          fromHRecord (toHRecord @STagged t1) == t1
    , testProperty "toHRecord . fromHRecord == castRecord" $
        \rec1 ->
          toHRecord (fromHRecord @STagged @Test1 @(Fields Test1) rec1) == castRecord rec1
    , testProperty "HKD-like conversion" \hInt hBool ->
        let hkd = MyHKD {..}
            ext =
              toHRecord @(HK.OnEntry Identity :: Symbol -> Type -> Type)
                hkd
         in (ext ^. recField #hInt === OnEntry hInt)
              .&&. (ext ^. recField #hBool === OnEntry hBool)
    ]

fieldNotFound :: Maybe a
fieldNotFound = unTagged <$> projField @"z" ascSimpleRecord1

test_projField :: TestTree
test_projField =
  testGroup
    "projField"
    [ testCase "Should return Nothing for non-existent field" do
        fieldNotFound @?= (Nothing :: Maybe Int)
        fieldNotFound @?= (Nothing :: Maybe Bool)
        fieldNotFound @?= (Nothing :: Maybe String)
    , testCase "Should throw type-error when the field type mismatched" do
        shouldThrowTypeMismatch (Just "a") typeMismatch
    ]

test_IsHRecord :: TestTree
test_IsHRecord =
  testGroup
    "IsHRecord"
    [ testProperty "Handles specialised instance well (Buz)" $
        \(buz :: Buz (Maybe String)) ->
          tabulate
            "Maybe cons"
            [chkMaybe $ buzX buz, chkMaybe $ buzY buz, chkMaybe $ buzZ buz]
            $ let toRec = toHRecord @(HK.OnEntry Maybe :: Symbol -> Type -> Type)
               in buz
                    === fromHRecord (toRec buz)
                    .&&. conjoin
                      [ toRec buz ^. HK.recField #buzX === OnEntry (buzX buz)
                      , toRec buz ^. HK.recField #buzY === OnEntry (buzY buz)
                      , toRec buz ^. HK.recField #buzZ === OnEntry (buzZ buz)
                      ]
    , testProperty "Handles specialised instance well (Buz0)" $
        \(buz :: Buz0) ->
          tabulate
            "Maybe cons"
            [chkMaybe $ ddd buz, chkMaybe $ ggg buz]
            $ buz
              === fromHRecord @(HK.OnEntry Maybe) @Buz0
                ( HK.emptyRec
                    HK.&+ #ddd
                    := OnEntry (ddd buz)
                    HK.&+ #ggg
                    := OnEntry (ggg buz)
                )
              .&&. let recs = toHRecord @(HK.OnEntry Maybe :: Symbol -> Type -> Type) buz
                    in conjoin
                        [ recs ^. recField #ddd === OnEntry (ddd buz)
                        , recs ^. recField #ggg === OnEntry (ggg buz)
                        ]
    ]

chkMaybe :: Maybe a -> String
chkMaybe Just {} = "Just"
chkMaybe Nothing {} = "Nothing"

test_mergeRec :: TestTree
test_mergeRec =
  testGroup
    "mergeRec"
    [ testProperty "from record-test" $
        \a c d g ->
          let r =
                HK.mergeRec
                  ( HK.emptyRec @Symbol @Type @(HK.OnEntry' Symbol Maybe)
                      HK.&+ #ccc
                      := HK.OnEntry (c :: Maybe Int)
                      HK.&+ #ggg
                      := HK.OnEntry (g :: Maybe Bool)
                  )
                  ( HK.emptyRec @Symbol @Type @(HK.OnEntry' Symbol Maybe)
                      HK.&+ #aaa
                      := HK.OnEntry (a :: Maybe Bool)
                      HK.&+ #ddd
                      := HK.OnEntry (d :: Maybe ())
                  )
           in conjoin
                [ r ^. recField #aaa === OnEntry a
                , r ^. recField #ccc === OnEntry c
                , r ^. recField #ddd === OnEntry d
                , r ^. recField #ggg === OnEntry g
                ]
    , testProperty
        "complex"
        \a b c d e g ->
          let r =
                HK.mergeRec
                  ( HK.singletonRec (MyDep (sKnownVal' @"eee") (e :: String))
                      HK.&+ #ccc
                      := MyDep sKnownVal' (c :: Int)
                      HK.&+ #ggg
                      := MyDep sKnownVal' (g :: Maybe Bool)
                  )
                  ( HK.emptyRec
                      HK.&+ #aaa
                      := MyDep sKnownVal' (a :: Bool)
                      HK.&+ #ddd
                      := MyDep sKnownVal' (d :: Maybe ())
                      HK.&+ #bbb
                      := MyDep sKnownVal' (b :: [Int])
                  )
           in conjoin
                [ r ^. recField #aaa === MyDep sKnownVal' a
                , r ^. recField #bbb === MyDep sKnownVal' b
                , r ^. recField #ccc === MyDep sKnownVal' c
                , r ^. recField #ddd === MyDep sKnownVal' d
                , r ^. recField #eee === MyDep sKnownVal' e
                , r ^. recField #ggg === MyDep sKnownVal' g
                ]
    , testCase "Rejects non-disjoint merging" do
        eith <- try $ evaluate $ force unmergeable
        case eith of
          Left te@(TypeError msg)
            | "OverlappingKey \"a\"" `T.isInfixOf` T.pack msg ->
                pure ()
            | otherwise ->
                assertFailure $
                  "Overlapping key exception expected, but got another type error:\n"
                    <> show te
          Right val ->
            assertFailure $
              "Type error expected, but got: "
                <> show val
    ]

data MyDep k n = MyDep (SSymbol k) n
  deriving (Show, Eq, Ord, Typeable, Generic)

test_recFieldTraversal :: TestTree
test_recFieldTraversal =
  testGroup
    "recFieldTraversal"
    [ testCase "Accessing non-existent field results in Nothing" do
        ascSimpleRecord1 ^? HK.recFieldTraversal @"d" @Bool @?= Nothing
        ascSimpleRecord1 ^? HK.recFieldTraversal @"d" @Int @?= Nothing
        ascSimpleRecord1 ^? HK.recFieldTraversal @"d" @String @?= Nothing
    , testCase "Mutating non-existent field results in identity" do
        (ascSimpleRecord1 & HK.recFieldTraversal @"d" @Bool .~ Tagged False)
          @?= ascSimpleRecord1
        (ascSimpleRecord1 & HK.recFieldTraversal @"d" @Int .~ Tagged 12)
          @?= ascSimpleRecord1
        (ascSimpleRecord1 & HK.recFieldTraversal @"d" @Void .~ Tagged undefined)
          @?= ascSimpleRecord1
    , testProperty "Mutating existent field with expected type updates properly" $
        \a a' b c ->
          let r = mkAscSimpleRecord1 a b c
           in (r & HK.recFieldTraversal @"a" .~ Tagged a')
                === mkAscSimpleRecord1 a' b c
    , testProperty
        "Mutating existent field with wrong type results in type error"
        \a a' b c ->
          let r = mkAscSimpleRecord1 a b c
           in ioProperty $ shouldThrowTypeMismatch (Just "a") $ mismatchUpdate a' r
    ]

shouldThrowTypeMismatch ::
  (NFData a, Show a) =>
  Maybe String ->
  a ->
  Assertion
shouldThrowTypeMismatch mlab a = do
  eith <- try $ evaluate $ force a
  case eith of
    Left te@(TypeError msg)
      | let tmsg = T.pack msg
      , (_, lft) <- T.breakOn "A label:" tmsg
      , not $ T.null lft
      , maybe
          True
          ( \lbl ->
              let rest = T.strip $ T.drop 8 lft
               in T.pack (show lbl) `T.isPrefixOf` rest
          )
          mlab
      , "must be associated with a type" `T.isInfixOf` lft ->
          pure ()
      | otherwise ->
          assertFailure $
            "Type mismatch error for value must be thrown, but got:"
              <> show te
    Right p ->
      assertFailure $
        "Type error expected, but got: " <> show p
