{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Data.TypeLevel.ListSpec where

import Data.Constraint (withDict)
import Data.List (sortOn)
import Data.Proxy (Proxy (Proxy))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Type.Equality ((:~:) (Refl))
import Data.TypeLevel.Known
import Data.TypeLevel.List (All, sLength, (%++))
import Data.TypeLevel.ListSpec.Cases
import Data.TypeLevel.ListSpec.Undeferred
import Data.TypeLevel.OrdMap (sConstList, sSortPermutation, (:::))
import qualified Data.TypeLevel.OrdMap as OM
import qualified Data.Typeable as DT
import GHC.Generics (Generic)
import GHC.TypeLits
  ( KnownSymbol,
    SomeSymbol (..),
    Symbol,
    someSymbolVal,
  )
import GHC.TypeNats (KnownNat, Nat, natVal, type (<=))
import Helpers
import Test.Tasty
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.QuickCheck
  ( Property,
    getNonNegative,
    ioProperty,
    tabulate,
    testProperty,
    (===),
  )
import Type.Reflection (SomeTypeRep, Typeable)

test_length_map :: TestTree
test_length_map = testProperty "Length commutes with Map" $
  \(xs :: [Integer]) ->
    let len = fromIntegral $ length xs
     in tabulate "length" [show len] $
          case promote @[Nat] (map (fromIntegral . abs) xs) of
            MkSomeSing lst ->
              withKnownNat' (sLength lst) $
                mapLen lst === len

test_illegal_length_map :: TestTree
test_illegal_length_map =
  testCase "Cannot derive length illegally" $
    shouldThrowTypeError $
      illegalMapLen (Proxy @'[])

test_trivalSort :: TestTree
test_trivalSort =
  testInspection "SortedBy respects SortBy" trivialSort

test_illegalSorts :: TestTree
test_illegalSorts =
  testGroup
    "SortedBy rejects illegal SortBy"
    [ expectInspectionFail "nested" nontrivialSort
    , expectInspectionFail "simple" nontrivialSort2
    ]

test_elimAllOMLookup :: TestTree
test_elimAllOMLookup =
  testGroup
    "Solver can eliminate AllOM + FromMaybe constraint"
    [ testCase "case1" $
        elimAllOMLookup (Proxy @'True) (Proxy @(OM.FromList '[])) (Proxy @Int)
          @?= "Int"
    , testCase "case2" $
        elimAllOMLookup (Proxy @'True) (Proxy @(OM.FromList '[ 'True OM.::: Bool])) (Proxy @Int)
          @?= "Bool"
    ]

test_showOrdMapType_Ok :: TestTree
test_showOrdMapType_Ok =
  testCase "AllOM elimination takes superclass constraints into account" $
    shownOrdMap
      @?= [ (DT.typeRep $ Proxy @Bool, DT.typeRep $ Proxy @1, 0)
          , (DT.typeRep $ Proxy @Int, DT.typeRep $ Proxy @5, 1)
          , (DT.typeRep $ Proxy @(Maybe ()), DT.typeRep $ Proxy @0, 2)
          ]

test_sortLabelType :: TestTree
test_sortLabelType =
  testProperty "withAllConstMap and foldMapOrdMap propagates constraints to key" $
    \(xs0 :: Set String) ->
      tabulate "size" [show $ Set.size xs0] $
        let xs = Set.toList xs0
         in ( case toKnownSymbols xs of
                MkKnownSymbols slist ->
                  withKnown' slist $
                    withKnown' (sSortPermutation $ sConstList slist) $
                      sortLabelTypeable slist
                        === sortOn fst (zip xs [0 ..])
            ) ::
              Property

data KnownSymbols where
  MkKnownSymbols ::
    (All Typeable syms, All KnownSymbol syms) =>
    SList syms ->
    KnownSymbols

toKnownSymbols ::
  [String] -> KnownSymbols
toKnownSymbols [] = MkKnownSymbols SNil
toKnownSymbols (sStr : rest) =
  case someSymbolVal sStr of
    SomeSymbol (_ :: Proxy symb) ->
      case toKnownSymbols rest of
        MkKnownSymbols syms ->
          MkKnownSymbols $ sKnownVal' @symb :% syms

test_listAssoc :: TestTree
test_listAssoc =
  testCase "Solver could prove associativity of list concatenation" $
    shouldNotThrowTypeError appAssoc

test_listFalseAssoc :: TestTree
test_listFalseAssoc =
  testCase "Solver could not prove wrong associativity" $
    shouldThrowTypeError appFalseAssoc

test_mapApply_Cons :: TestTree
test_mapApply_Cons =
  testProperty "MapApply distributes over append and cons" $
    \xs (x :: Integer) ys ->
      ( case ( promote @[Nat] $ map fromInteger xs
             , promote @Nat (fromIntegral x)
             , promote @[Nat] $ map fromInteger ys
             ) of
          (MkSomeSing xs', MkSomeSing nat', MkSomeSing ys') ->
            case mapApplyDistrib xs' ys' nat' of
              Refl -> True
      ) ::
        Bool

test_False_mapApply_Cons :: TestTree
test_False_mapApply_Cons =
  testCase "MapApply refutes inappropriate distribution" $
    shouldThrowTypeError $
      mapApplyFalseDistrib (Proxy @[1, 2, 3]) (Proxy @[4, 5, 6]) (Proxy @12)

data Foo n where
  TheOne :: Foo 1
  The42 :: Foo 42
  TheThree :: Foo 3

instance Show (Foo 1) where
  showsPrec _ TheOne = showString "TheOne"

instance Show (Foo 42) where
  showsPrec _ The42 = showString "The42"

instance Show (Foo 3) where
  showsPrec _ TheThree = showString "TheThree"

test_showMap :: TestTree
test_showMap =
  testCase "Map and All commutes" $
    showMap (Proxy @'[42, 1, 3]) TheOne @?= "TheOne"

test_typeRepList :: TestTree
test_typeRepList =
  testCase "typeRepList" $
    typeRepList (Proxy @'[Int, IO Bool, String])
      @?= [ DT.typeRep (Proxy @Int)
          , DT.typeRep (Proxy @(IO Bool))
          , DT.typeRep (Proxy @String)
          ]

test_typeRepList_symbols :: TestTree
test_typeRepList_symbols = testProperty "typeRepList" $ \strs ->
  ( case toKnownSymbols strs of
      MkKnownSymbols (symbs :: SList syms) ->
        withKnownNat' (sLength symbs) $
          typeRepList (Proxy @syms)
            === symsTypeRepList symbs
  ) ::
    Property

symsTypeRepList ::
  All Typeable syms => SList (syms :: [Symbol]) -> [SomeTypeRep]
symsTypeRepList SNil = []
symsTypeRepList (x :% xs) =
  DT.typeRep x : symsTypeRepList xs

class GoodNat (a :: Nat) where
  isGood :: Foo a -> String

instance GoodNat 1 where
  isGood = show

instance GoodNat 3 where
  isGood = show

instance GoodNat 42 where
  isGood = show

test_myElimFromAll :: TestTree
test_myElimFromAll =
  testCase "List solver can resolve All'd constraint from Member polyrmorphically" $
    withDict (myElimFromAll (Proxy @GoodNat) (Proxy @1) (Proxy @'[42, 1, 3])) $
      isGood TheOne @?= "TheOne"

test_splitAtApply :: TestTree
test_splitAtApply =
  testProperty "Can solve complex equation involving Take, Drop and Map" $
    \(x :: Maybe String) (y :: String) (xs :: [String]) ->
      case (promote @(Maybe Symbol) x, promote @Symbol y, promote @[Symbol] xs) of
        ( MkSomeSing (_ :: Sing ms)
          , MkSomeSing (_ :: Sing sym)
          , MkSomeSing (_ :: Sing xs)
          ) ->
            ioProperty $
              shouldNotThrowTypeError $
                splitAtApply (Proxy @ms) (Proxy @sym) (Proxy @xs)

class GoodOver h a where
  goodOver :: proxy h -> proxy' a -> String

data Qux deriving (Typeable, Generic)

data Bar deriving (Typeable, Generic)

data Duz deriving (Typeable, Generic)

type GoodDic =
  OM.FromList
    '[ Qux ::: 42
     , Bar ::: 4
     , Duz ::: 999
     ]

instance GoodOver Qux 42 where
  goodOver _ _ = "Qux 42"

instance GoodOver Duz n where
  goodOver _ _ = "Qux <>"

instance (KnownNat n, n <= 5) => GoodOver Bar n where
  goodOver _ = ("Bar " <>) . show . natVal

test_trivialOM :: TestTree
test_trivialOM =
  testCase "OrdMap solver can resolve All'd constraint from Member polyrmorphically" $
    withDict (trivialOM (Proxy @GoodOver) (Proxy @GoodDic) (Proxy @Qux)) $
      goodOver (Proxy @Qux) (Proxy @42) @?= "Qux 42"

test_sAppend :: TestTree
test_sAppend =
  testProperty "(%++) appends two type-level lists correctly" $
    \(map (fromInteger . getNonNegative) -> xs)
     (map (fromInteger . getNonNegative) -> ys) ->
        case (promote @[Nat] xs, promote @[Nat] ys) of
          (MkSomeSing sxs, MkSomeSing sys) ->
            let xsys = demote $ sxs %++ sys
             in xsys === (xs ++ ys)
