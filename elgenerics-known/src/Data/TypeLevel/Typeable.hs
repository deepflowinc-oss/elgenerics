{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.TypeLevel.Typeable (
  PTypeRep (..),
  TypeRepOf,
  CmpTypeRep,
  ShowTypeRep,
  deriveTypeRep,
  sTypeRepOf,
  SPTypeRep (..),
  DynDCon,
) where

import Control.Monad
import Data.Foldable
import Data.Int
import Data.Kind
import Data.Maybe
import Data.Sequence qualified as Seq
import Data.Type.Equality
import Data.TypeLevel.Known
import Data.TypeLevel.Monoid
import Data.TypeLevel.Nat
import Data.Word
import GHC.Generics
import GHC.TypeLits
import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Desugar
import TH.ReifySimple
import Type.Reflection hiding (Con)
import Type.Reflection qualified as TyRep
import Unsafe.Coerce (unsafeCoerce)

data PTypeRep
  = TySym Symbol
  | TyNat Nat
  | Con Symbol Symbol Symbol
  | TyApp PTypeRep PTypeRep
  | TyFun PTypeRep PTypeRep
  deriving (Typeable)

defineSingletons ''PTypeRep
deriveKnown ''PTypeRep
deriveShowSing ''PTypeRep
deriveSTestEquality ''PTypeRep

type PrimOrRep :: forall k. k -> Type -> Type
type family PrimOrRep (a :: k) :: Type -> Type where
  PrimOrRep Natural = D1 ('MetaData "Natural" "GHC.Num.Natural" "ghc-bignum" 'False) V1
  PrimOrRep Symbol = D1 ('MetaData "Symbol" "GHC.Types" "ghc-prim" 'False) V1
  PrimOrRep Int = D1 ('MetaData "Int" "GHC.Types" "ghc-prim" 'False) V1
  PrimOrRep Word = D1 ('MetaData "Word" "GHC.Types" "ghc-prim" 'False) V1
  PrimOrRep Float = D1 ('MetaData "Float" "GHC.Types" "ghc-prim" 'False) V1
  PrimOrRep Double = D1 ('MetaData "Double" "GHC.Types" "ghc-prim" 'False) V1
  PrimOrRep Char = D1 ('MetaData "Char" "GHC.Types" "ghc-prim" 'False) V1
  PrimOrRep Word8 = D1 ('MetaData "Word8" "GHC.Word" "base" 'False) V1
  PrimOrRep Word16 = D1 ('MetaData "Word16" "GHC.Word" "base" 'False) V1
  PrimOrRep Word32 = D1 ('MetaData "Word32" "GHC.Word" "base" 'False) V1
  PrimOrRep Word64 = D1 ('MetaData "Word64" "GHC.Word" "base" 'False) V1
  PrimOrRep Int8 = D1 ('MetaData "Int8" "GHC.Int" "base" 'False) V1
  PrimOrRep Int16 = D1 ('MetaData "Int16" "GHC.Int" "base" 'False) V1
  PrimOrRep Int32 = D1 ('MetaData "Int32" "GHC.Int" "base" 'False) V1
  PrimOrRep Int64 = D1 ('MetaData "Int64" "GHC.Int" "base" 'False) V1
  PrimOrRep Integer =
    D1 ('MetaData "Integer" "GHC.Integer.Type" "integer-gmp" 'False) V1
  PrimOrRep a = Rep a
  PrimOrRep (a :: k) = DynDCon k a

type family DynDCon k (a :: k) :: Type -> Type

deriveTypeRep ::
  Name -> DecsQ
deriveTypeRep name = do
  DataType {} <- reifyDataType name
  Just (DTyConI (DDataD newOrData _ _ _tyVars _mKind cons _) _) <-
    dsReify name
  fmap (sweeten . concat) $
    forM cons $ \dcon@(DCon _ _ dcName _ _) -> do
      let (params, retType) = dconParamRetType dcon
      body <- desugar =<< buildDynDCon newOrData dcon
      loop dcName Seq.empty params retType body []
  where
    loop dcName args params retType body acc =
      let dsig = foldr (\l r -> (DAppT DArrowT l) `DAppT` r) retType params
          applied = foldl' DAppT (DConT dcName) args
          dsyn =
            DTySynInstD $
              DTySynEqn
                Nothing
                (DConT ''DynDCon `DAppT` dsig `DAppT` applied)
                body
       in case params of
            [] -> pure $ dsyn : acc
            (p : ps) -> do
              v <- newName "v"
              let p' = DVarT v `DSigT` p
              loop dcName (args Seq.|> p') ps retType body (dsyn : acc)

dconParamRetType ::
  DCon -> ([DType], DType)
dconParamRetType (DCon _ _ _ flds retTy) = do
  (decodeConFields flds, retTy)

decodeConFields :: DConFields -> [DType]
decodeConFields (DNormalC _ bTys) = map snd bTys
decodeConFields (DRecC vbtys) =
  map (\(_, _, ty) -> ty) vbtys

buildDynDCon ::
  NewOrData -> DCon -> TypeQ
buildDynDCon newOr (DCon _ _ dcName _ _) = do
  let modName = fromMaybe "<UNKNOWN>" $ nameModule dcName
      pkgName = fromMaybe "<UNKNOWN>" $ namePackage dcName
      isNew = case newOr of
        Newtype -> [t|'True|]
        Data -> [t|'False|]
  [t|
    D1
      ( 'MetaData
          $(litT $ strTyLit $ nameBase dcName)
          $(litT $ strTyLit $ modName)
          $(litT $ strTyLit $ pkgName)
          $(isNew)
      )
      V1
    |]

type TypeRepOf :: k -> PTypeRep
type family TypeRepOf (a :: k) :: PTypeRep where
  TypeRepOf (n :: Nat) = 'TyNat n
  TypeRepOf (sym :: Symbol) = 'TySym sym
  TypeRepOf a = TypeRepOfAux (ToCon (PrimOrRep a)) a

type TypeRepOfAux :: PTypeRep -> k -> PTypeRep
type family TypeRepOfAux (rep :: PTypeRep) (a :: k) :: PTypeRep where
  TypeRepOfAux _ (a -> b) = 'TyFun (TypeRepOf a) (TypeRepOf b)
  TypeRepOfAux rep (f a) = 'TyApp (TypeRepOfAux rep f) (TypeRepOf a)
  TypeRepOfAux rep _ = rep

type family ToCon (f :: k -> Type) :: PTypeRep where
  ToCon (D1 ('MetaData l m p 'False) _) = 'Con l m p

type CmpTypeRep l r = CmpTypeRepAux (l == r) l r

type family
  CmpTypeRepAux (p :: Bool) (l :: PTypeRep) (r :: PTypeRep) ::
    Ordering
  where
  CmpTypeRepAux 'True t t = 'EQ
  CmpTypeRepAux 'False ('TySym l) ('TySym r) = CmpSymbol l r
  CmpTypeRepAux 'False ('TySym _) _ = 'LT
  CmpTypeRepAux 'False ('TyNat _) ('TySym _) = 'GT
  CmpTypeRepAux 'False ('TyNat l) ('TyNat r) = CmpNat l r
  CmpTypeRepAux 'False ('TyNat _) _ = 'LT
  CmpTypeRepAux 'False ('Con _ _ _) ('TySym _) = 'GT
  CmpTypeRepAux 'False ('Con _ _ _) ('TyNat _) = 'GT
  CmpTypeRepAux 'False ('Con l1 l2 l3) ('Con r1 r2 r3) =
    CmpSymbol l1 r1 <> CmpSymbol l2 r2 <> CmpSymbol l3 r3
  CmpTypeRepAux 'False ('Con _ _ _) _ = 'LT
  CmpTypeRepAux 'False ('TyApp _ _) ('TySym _) = 'GT
  CmpTypeRepAux 'False ('TyApp _ _) ('TyNat _) = 'GT
  CmpTypeRepAux 'False ('TyApp _ _) ('Con _ _ _) = 'GT
  CmpTypeRepAux 'False ('TyApp l1 l2) ('TyApp r1 r2) =
    CmpTypeRepAux (l1 == r1) l1 r1 <> CmpTypeRepAux (l2 == r2) l2 r2
  CmpTypeRepAux 'False ('TyApp _ _) ('TyFun _ _) = 'LT
  CmpTypeRepAux 'False ('TyApp _ _) _ = 'GT
  CmpTypeRepAux 'False ('TyFun l r) ('TyFun l' r') =
    CmpTypeRepAux (l == l') l l' <> CmpTypeRepAux (r == r') r r'
  CmpTypeRepAux 'False ('TyFun l r) _ = 'GT

type ShowTypeRep a = ShowTypeRepAux 'False a

type family ShowTypeRepAux (b :: Bool) (tyRep :: PTypeRep) :: Symbol where
  ShowTypeRepAux _ ('TyNat n) = ShowNat n
  ShowTypeRepAux _ ('TySym n) = n
  ShowTypeRepAux _ ('Con l _ _) = l
  ShowTypeRepAux 'False ('TyApp l r) =
    ShowTypeRepAux 'False l <> " " <> ShowTypeRepAux 'True r
  ShowTypeRepAux 'True ('TyApp l r) =
    "(" <> ShowTypeRepAux 'False l <> " " <> ShowTypeRepAux 'True r <> ")"
  ShowTypeRepAux 'True ('TyFun l r) =
    "(" <> ShowTypeRepAux 'False ('TyFun l r) <> ")"
  ShowTypeRepAux 'False ('TyFun l r) =
    ShowTypeRepAux 'True l <> " -> " <> ShowTypeRepAux 'False r

sTypeRepOf :: Sing (a :: Type) -> Sing (TypeRepOf a)
sTypeRepOf rep = withKnown' rep $ liftTypeRep rep

liftTypeRep ::
  forall k a.
  (Typeable k) =>
  TypeRep (a :: k) ->
  Sing (TypeRepOf a)
liftTypeRep rep =
  let tCon = TyRep.typeRepTyCon rep
   in case testEquality (typeRep @Nat) (typeRep @k) of
        Just Refl -> case promote @Nat (read $ tyConName tCon) of
          MkSomeSing sn -> STyNat $ unsafeCoerce sn
        Nothing ->
          case testEquality (typeRep @Symbol) (typeRep @k) of
            Just Refl ->
              case promote @Symbol $ read $ tyConName tCon of
                MkSomeSing ssymb -> STySym $ unsafeCoerce ssymb
            Nothing ->
              case rep of
                TyRep.App l r ->
                  TyRep.withTypeable (typeRepKind l) $
                    TyRep.withTypeable (typeRepKind r) $
                      unsafeCoerce $
                        STyApp (liftTypeRep l) (liftTypeRep r)
                TyRep.Con con ->
                  case ( promote $ tyConName con
                       , promote $ tyConModule con
                       , promote $ tyConPackage con
                       ) of
                    (MkSomeSing l, MkSomeSing m, MkSomeSing n) ->
                      unsafeCoerce $
                        SCon l m n
                TyRep.Fun l r ->
                  TyRep.withTypeable (typeRepKind l) $
                    TyRep.withTypeable (typeRepKind r) $
                      unsafeCoerce $
                        STyFun (liftTypeRep l) (liftTypeRep r)
