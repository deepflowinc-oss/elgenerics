{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
module Data.TypeLevel.List.Solver.Syntax
  ( WType(..), FunType(..), IsWrapped,
    isUnknownTerm, isUnknownC,
    Syntax(..), Ghc, Debug, WithCtLoc(..),
    WKind,
    Constr,
    Constr'
      ( EqType, KnownNat, KnownTyList, SortedBy, Known,
        Monotone, PreservesLength, UnknownC, Member, All,
        AllOM, MemberOM, MaybeC
      ),
    Term,
    Term'
      ( .., Compare2, Map, Length, SortByAux, PromotedTuple,
        Indexed, EmptyList, PromotedJust, Index, ElemAt, UnknownTerm,
        Take, Drop, AppList, Apply, OMIndex, SizeOM, ToListOM,
        FromMaybe, MapMaybeApp,
        UnknownTyConApp, ToListAuxOM, LookupWithIndexOM, Lookup'OM
      ),
    (-->), (~>), listTy,
    fromConstr, toConstr, fromTerm, toTerm,
    deconsPred, substTerm,
    SymbolTable(..), setupSymbolTable
  ) where
import Control.Applicative
import Control.Lens        hiding (Indexed)
import Data.Data           (Data, Typeable)
import Data.Function
import Data.Maybe
import GHC.Generics
import GHC.TcPluginM.Extra
import Data.TypeLevel.List.Solver.Utils
#if MIN_VERSION_ghc(9,0,1)
import GHC.Core.Class
import GHC.Plugins          hiding ((<>))
import GHC.Builtin.Names
import GHC.Tc.Plugin           hiding (newWanted)
import GHC.Core.Predicate
import GHC.Tc.Types.Constraint
import Control.Arrow ((>>>))
#else
import Class
import GhcPlugins          hiding ((<>))
import PrelNames
import TcPluginM           hiding (newWanted)
import Predicate
import Constraint
import TyCoRep (mkFunTy)
#endif

type WKind = WType
newtype WType = WType { runWType :: Type }
    deriving (Typeable, Data)
newtype WTyCon = WTyCon { runWTyCon :: TyCon }
    deriving (Typeable, Data)

instance Show WTyCon where
  showsPrec d = showParen (d > 10) . showString . showSDocExplicit  . ppr . runWTyCon
instance Eq WTyCon where
  (==) = fmap (== EQ) . (nonDetCmpTc `on` runWTyCon)
instance Ord WTyCon where
  compare = nonDetCmpTc `on` runWTyCon
instance Show WType where
  showsPrec d (WType ty) = showParen (d > 10) $
    showString $ showSDocUnsafe $ ppr ty

instance Eq WType where
  (==) = eqType `on` runWType

instance Ord WType where
  compare = nonDetCmpType `on` runWType

data FunType = Bare | Uncurry
  deriving (Read, Show, Eq, Ord, Generic, Data, Typeable)
type IsWrapped = Bool
newtype WEqRel = WEqRel { runWEqRel :: EqRel }
  deriving newtype (Eq, Ord)
instance Show WEqRel where
  showsPrec _ = showString . showSDocUnsafe . ppr . runWEqRel

data Constr' term
  = EqType' WEqRel term term
  | KnownNat term
  | KnownTyList' WKind term
  | SortedBy' WKind term term
  | Monotone' FunType WKind WKind term term term
  | PreservesLength' term
  | Member' IsWrapped WKind term term
  | All' WKind term term
  | UnknownC' WType
  | AllOM' WKind WKind term term
  | MemberOM' IsWrapped WKind WKind term term
  | MaybeC' WKind term term
  | Known' WKind term
    deriving (Eq, Ord, Show, Functor, Foldable)
type Constr = Constr' Term

{-# COMPLETE
  EqType, KnownNat, KnownTyList, SortedBy, Member, MemberOM,
  Monotone, PreservesLength, All, AllOM, UnknownC, Known, MaybeC #-}
class
  ( Data a,
    Data (KindOf a), Eq (KindOf a), Ord (KindOf a), Show (KindOf a),
    Data (TypeOf a), Eq (TypeOf a), Ord (TypeOf a), Show (TypeOf a),
    Data (TyConOf a), Eq (TyConOf a), Ord (TyConOf a), Show (TyConOf a)
  ) => Syntax a where
  type KindOf a
  type TypeOf a
  type TyConOf a

data Ghc deriving (Typeable, Data)
instance Syntax Ghc where
  type KindOf Ghc = WKind
  type TypeOf Ghc = WType
  type TyConOf Ghc = WTyCon

data Debug deriving (Typeable, Data)

instance Syntax Debug where
  type KindOf Debug = String
  type TypeOf Debug = String
  type TyConOf Debug = String

type Term = Term' Ghc
data Term' suite
  = Compare2' (KindOf suite)
  | TyNat Integer
  | Map' FunType (KindOf suite) (KindOf suite) (Term' suite) (Term' suite)
  | Length' (KindOf suite) (Term' suite)
  | SortByAux' (KindOf suite) (Term' suite) (Term' suite) (Term' suite)
  | Indexed' (KindOf suite) (Term' suite)
  | EmptyList' (KindOf suite)
  | PromotedJust' (KindOf suite) (Term' suite)
  | PromotedTuple' (KindOf suite) (KindOf suite) (Term' suite) (Term' suite)
  | Index' (KindOf suite) (Term' suite) (Term' suite)
  | OMIndex' (KindOf suite) (KindOf suite) (Term' suite) (Term' suite)
    -- key val key (OrdMap key val)
  | ElemAt' (KindOf suite) (Term' suite) (Term' suite)
  | Drop' (KindOf suite) (Term' suite) (Term' suite)
  | Take' (KindOf suite) (Term' suite) (Term' suite)
  | AppList' (KindOf suite) (Term' suite) (Term' suite)
  | UnknownTyConApp' (TyConOf suite) [(Term' suite)]
  | Apply' FunType (Term' suite) (Term' suite)
  | SizeOM' (KindOf suite) (KindOf suite) (Term' suite)
  | ToListOM' (KindOf suite) (KindOf suite) (Term' suite)
  | ToListAuxOM' (KindOf suite) (KindOf suite) (Term' suite) (Term' suite)
  | LookupWithIndexOM' (KindOf suite) (KindOf suite) (Term' suite) (Term' suite)
  | Lookup'OM' (KindOf suite) (KindOf suite) (Term' suite) (Term' suite)
  | FromMaybe' (KindOf suite) (Term' suite) (Term' suite)
  | MapMaybeApp' (KindOf suite)(KindOf suite) (Term' suite) (Term' suite)
  | UnknownTerm' (TypeOf suite)
    deriving (Generic)

deriving instance Syntax a => Typeable (Term' a)
deriving instance Syntax a => Data (Term' a)
deriving instance Syntax a => Show (Term' a)
deriving instance Syntax a => Eq (Term' a)
deriving instance Syntax a => Ord (Term' a)

deriving anyclass instance Syntax suite => Plated (Term' suite)

{-# COMPLETE
    Compare2, TyNat, Map, Length, SortByAux,
    Indexed, EmptyList, PromotedJust, PromotedTuple, Index, OMIndex, ElemAt, Drop, Take, AppList, MapMaybeApp,
    Apply, SizeOM, ToListAuxOM, LookupWithIndexOM, Lookup'OM,
    UnknownTerm, UnknownTyConApp, FromMaybe
  #-}

pattern PromotedJust :: Kind -> Term -> Term
pattern PromotedJust k v = PromotedJust' (WType k) v

pattern PromotedTuple :: Kind -> Kind -> Term -> Term -> Term
pattern PromotedTuple a b l r = PromotedTuple' (WType a) (WType b) l r

pattern KnownTyList :: Kind -> Term -> Constr
pattern KnownTyList k t = KnownTyList' (WType k) t

pattern Member :: IsWrapped -> Kind -> Term -> Term -> Constr
pattern Member b k x xs = Member' b (WType k) x xs

pattern MemberOM :: IsWrapped -> Kind -> Kind -> Term -> Term -> Constr
pattern MemberOM b k v x xs = MemberOM' b (WType k) (WType v) x xs

pattern All :: Kind -> Term -> Term -> Constr
pattern All k x xs = All' (WType k) x xs

pattern AllOM :: Kind -> Kind -> Term -> Term -> Constr
pattern AllOM k k' x xs = AllOM' (WType k) (WType k') x xs

pattern EqType :: EqRel -> Term -> Term -> Constr
pattern EqType b t u = EqType' (WEqRel b) t u

pattern SortedBy :: Kind -> Term -> Term -> Constr
pattern SortedBy k cmp xs = SortedBy' (WType k) cmp xs

pattern Monotone :: FunType -> Kind -> Kind -> Term -> Term -> Term -> Constr
pattern Monotone fty k k' f cmp cmp' =
  Monotone' fty (WType k) (WType k') f cmp cmp'

pattern PreservesLength :: Term -> Constr
pattern PreservesLength t =
  PreservesLength' t

pattern UnknownC :: Type -> Constr
pattern UnknownC ty =
  UnknownC' (WType ty)

pattern MaybeC :: Type -> Term -> Term -> Constr
pattern MaybeC kind c may = MaybeC' (WType kind) c may


pattern Known :: Type -> Term -> Constr
pattern Known kind x = Known' (WType kind) x

pattern Compare2 :: Kind -> Term
pattern Compare2 k = Compare2' (WType k)
pattern Map :: FunType -> Kind -> Kind -> Term -> Term -> Term
pattern Map fty k k' t u = Map' fty (WType k) (WType k') t u
pattern Length :: Kind -> Term -> Term
pattern Length k x = Length' (WType k) x
pattern SortByAux :: Kind -> Term -> Term -> Term -> Term
pattern SortByAux k a b c = SortByAux' (WType k) a b c
pattern Indexed :: Kind -> Term -> Term
pattern Indexed k xs = Indexed' (WType k) xs
pattern EmptyList :: Kind -> Term
pattern EmptyList k = EmptyList' (WType k)
pattern Index :: Kind -> Term -> Term -> Term
pattern Index k x xs = Index' (WType k) x xs
pattern OMIndex :: Kind -> Kind -> Term -> Term -> Term
pattern OMIndex key val x xs = OMIndex' (WType key) (WType val) x xs
pattern ElemAt :: Kind -> Term -> Term -> Term
pattern ElemAt k n xs = ElemAt' (WType k) n xs

pattern Drop :: Kind -> Term -> Term -> Term
pattern Drop k n xs = Drop' (WType k) n xs
pattern Take :: Kind -> Term -> Term -> Term
pattern Take k n xs = Take' (WType k) n xs
pattern AppList :: Kind -> Term -> Term -> Term
pattern AppList k xs ys = AppList' (WType k) xs ys

pattern FromMaybe :: Kind -> Term -> Term -> Term
pattern FromMaybe k xs ys = FromMaybe' (WType k) xs ys
pattern MapMaybeApp :: Kind -> Kind -> Term -> Term -> Term
pattern MapMaybeApp k k' xs ys = MapMaybeApp' (WType k)(WType k') xs ys

pattern UnknownTyConApp :: TyCon -> [Term] -> Term
pattern UnknownTyConApp con ts = UnknownTyConApp' (WTyCon con) ts

pattern Apply :: FunType -> Term -> Term -> Term
pattern Apply funType l r = Apply' funType l r

pattern UnknownTerm :: Type -> Term
pattern UnknownTerm k = UnknownTerm' (WType k)

pattern SizeOM :: Kind -> Kind -> Term -> Term
pattern SizeOM k v dic = SizeOM' (WType k) (WType v) dic

pattern ToListOM :: Kind -> Kind -> Term -> Term
pattern ToListOM k v dic = ToListOM' (WType k) (WType v) dic

pattern ToListAuxOM :: Kind -> Kind -> Term -> Term -> Term
pattern ToListAuxOM k v acc dic = ToListAuxOM' (WType k) (WType v) acc dic

pattern LookupWithIndexOM :: Kind -> Kind -> Term -> Term -> Term
pattern LookupWithIndexOM k v l dic = LookupWithIndexOM' (WType k) (WType v) l dic

pattern Lookup'OM :: Kind -> Kind -> Term -> Term -> Term
pattern Lookup'OM k v l dic = Lookup'OM' (WType k) (WType v) l dic

toConstr :: SymbolTable -> PredType -> Constr
toConstr stbl@STbl{..} ty =
  let unk = UnknownC ty
  in fromMaybe unk $
    case classifyPredType ty of
      ClassPred cls ts -> buildClass (classTyCon cls) ts
      EqPred rel l r   -> Just $ EqType rel (toTerm stbl l) (toTerm stbl r)
      _                -> uncurry buildClass =<< deconsPred ty
  where
    buildClass cls [n]
      | cls == knownNatTyCon
      = case toTerm stbl n of
          Index k x xs ->
            Just $ Member False k x xs
          Length k xs ->
            Just $ KnownTyList k xs
          t -> Just $ KnownNat t
    buildClass cls [x, xs]
      | cls == memberTyCon =
          Just $ Member True (typeKind x) (toTerm stbl x) (toTerm stbl xs)
    buildClass cls [k, x]
      | cls == knownTyCon =
          Just $ Known k  (toTerm stbl x)
    buildClass cls [key, val, x, xs]
      | cls == omMemberTyCon
      = Just $ MemberOM True key val (toTerm stbl x) (toTerm stbl xs)
    buildClass cls [k, c, xs]
      | cls == allTyCon
      = Just $ All k (toTerm stbl c) (toTerm stbl xs)
    buildClass cls [k, c, xs]
      | cls == maybeCTyCon
      = Just $ MaybeC k (toTerm stbl c) (toTerm stbl xs)
    buildClass cls [k, v, c, xs]
      | cls == allOMTyCon
      = Just $ AllOM k v (toTerm stbl c) (toTerm stbl xs)
    buildClass cls [_, f]
      | cls == presLenTyCon
      = Just
      $ PreservesLength $ toTerm stbl f
    buildClass cls [k, cmp, xs]
      | cls `elem` [classTyCon sortedByCls, sortedByAuxTyCon]
      = Just
      $ SortedBy k (toTerm stbl cmp) (toTerm stbl xs)
    buildClass cls [k, k', f, cmp, cmp']
      | Just fty <- lookup cls $ monotoneDic stbl
      = Just
      $ Monotone fty k k'
          (toTerm stbl f)
          (toTerm stbl cmp) (toTerm stbl cmp')
    buildClass _ _ = Nothing

fromConstr :: SymbolTable -> Constr -> PredType
fromConstr stbl@STbl{} (EqType rel l r) =
  let (a, b) = (fromTerm stbl l, fromTerm stbl r)
      mk = case rel of { NomEq -> mkPrimEqPred ; ReprEq -> mkReprPrimEqPred }
  in mk a b
fromConstr stbl@STbl{..} (AllOM key val constr dic) =
  mkTyConApp allOMTyCon [key, val, fromTerm stbl constr, fromTerm stbl dic]
fromConstr stbl@STbl{..} (KnownNat n) =
  mkTyConApp knownNatTyCon [fromTerm stbl n]
fromConstr stbl@STbl{..} (Known k x )=
  mkTyConApp knownTyCon [k, fromTerm stbl x]
fromConstr stbl@STbl{..} (All k c xs) =
  mkTyConApp allTyCon [k, fromTerm stbl c, fromTerm stbl xs]
fromConstr stbl (Member False k x xs) =
  fromConstr stbl $ KnownNat $ Index k x xs
fromConstr stbl@STbl{..} (Member True k x xs) =
  mkTyConApp memberTyCon [k, fromTerm stbl x, fromTerm stbl xs]
fromConstr stbl@STbl{..} (MemberOM _ k v x xs) =
  mkTyConApp omMemberTyCon [k, v, fromTerm stbl x, fromTerm stbl xs]
fromConstr stbl@STbl{} (KnownTyList k xs) =
  fromConstr stbl (KnownNat (Length k xs))
fromConstr stbl@STbl{..} (SortedBy k cmp xs) =
  mkTyConApp (classTyCon sortedByCls)
    [k, fromTerm stbl cmp , fromTerm stbl xs]
fromConstr stbl@STbl{..} (Monotone fty k k' f cmp cmp') =
  let con = case fty of
        Bare    -> monotoneTyCon
        Uncurry -> monotoneAppTyCon
  in mkTyConApp con
      [ k, k'
      , fromTerm stbl f
      , fromTerm stbl cmp
      , fromTerm stbl cmp'
      ]
fromConstr stbl@STbl{..} (PreservesLength p) =
  let x = fromTerm stbl p
  in mkTyConApp presLenTyCon [typeKind x, x]
fromConstr stbl@STbl{..} (MaybeC k c may) =
  mkTyConApp maybeCTyCon [k, fromTerm stbl c, fromTerm stbl may]
fromConstr _ (UnknownC ty) = ty

toTerm :: SymbolTable -> Type -> Term
toTerm stbl@STbl{..} ty =
  fromMaybe (UnknownTerm ty) $
      TyNat <$> isNumLitTy ty
  <|> case splitTyConApp_maybe ty of
        Just (con, [x])
          | con == compare2TyCon
            -> Just $ Compare2 x
        Just (con, [k])
          | con == promotedNilDataCon
          -> Just $ EmptyList k
        Just (con, [k, v])
          | con == promotedJustDataCon
          -> Just $ PromotedJust k (toTerm stbl v)
        Just (con, [k, as, bs])
          | con == appListTyCon
            -> Just $ AppList k (toTerm stbl as) (toTerm stbl bs)
        Just (con, [k, v, dic])
          | con == omToListTyCon
          -> Just $ ToListOM k v (toTerm stbl dic)
        Just (con, [k, v, acc, dic])
          | con == omToListAuxTyCon
          , Just (niler, _) <- splitTyConApp_maybe acc
          , niler == promotedNilDataCon
          -> Just $ ToListAuxOM k v (toTerm stbl acc) (toTerm stbl dic)
        Just (con, [a,b,l,r])
          | con == promotedTupleDataCon Boxed 2
          -> Just $ PromotedTuple a b (toTerm stbl l) (toTerm stbl r)
        Just (con, [k, k', f, xs])
          | Just fty <- lookup con (mapDic stbl)
            -> let (fr, t) =
#if MIN_VERSION_ghc(8,8,1)
                      case fty of
                        Bare    -> (k', k)
                        Uncurry -> (k, k')
#else
                      case fty of
                        Bare    -> (k, k')
                        Uncurry -> (k', k)
#endif
               in Just $ Map fty fr t
                  (toTerm stbl f) $ toTerm stbl xs
          | con == applyTyCon
            -> Just $ Apply Uncurry (toTerm stbl f) (toTerm stbl xs)
        Just (con, [k, x])
          | con == lengthTyCon
            -> Just $ Length k $
                toTerm stbl x
          | con == indexedTyCon
            -> Just $ Indexed k $
                toTerm stbl x
        Just (con, [k, cmp, n, xs])
          | con == sortByAuxTyCon
            -> Just $ SortByAux k
                (toTerm stbl cmp)
                (toTerm stbl n)
                (toTerm stbl xs)
        Just (con, [k, x, xs, rest])
          | con == indexTyCon'
          , Just (niler, [k']) <- splitTyConApp_maybe rest
          , niler == promotedNilDataCon && k `eqType` k'
            -> Just $ Index k
                (toTerm stbl x)
                (toTerm stbl xs)
        Just (con, [k,v,l,dic])
          | con == lookupWithIdxTyCon
            -> Just $ LookupWithIndexOM k v (toTerm stbl l) (toTerm stbl dic)
        Just (con, [k, x, xs])
          | con == elemAtTyCon
            -> Just $ ElemAt k (toTerm stbl x) (toTerm stbl xs)
        Just (con, [k, x, xs])
          | con == fromMaybeTyCon
            -> Just $ FromMaybe k (toTerm stbl x) (toTerm stbl xs)
        Just (con, [k, k', f, xs])
          | con == mapMaybeTyCon
            -> Just $ MapMaybeApp k  k' (toTerm stbl f) (toTerm stbl xs)
        Just (con, [k, n, xs])
          | con == dropTyCon
            -> Just $ Drop k (toTerm stbl n) (toTerm stbl xs)
          | con == takeTyCon
            -> Just $ Take k (toTerm stbl n) (toTerm stbl xs)
        Just (con, args) ->
            Just $ UnknownTyConApp con $ map (toTerm stbl) args
        _ -> Nothing
    <|> case splitAppTy_maybe ty of
          Just (l, r) ->
            Just $ Apply Bare (toTerm stbl l) (toTerm stbl r)
          _           -> Nothing

fromTerm :: SymbolTable -> Term -> Type
fromTerm STbl{..} = go
  where
    go (Compare2 k) = mkTyConApp compare2TyCon [k]
    go (TyNat n) = mkNumLitTy n
    go (PromotedTuple a b l r) =
      mkTyConApp (promotedTupleDataCon Boxed 2)
      [a, b, go l, go r]
    go (Map fty k k' f xs) =
      let (con, lKind, rKind) = case fty of
#if MIN_VERSION_ghc(8,8,1)
            Bare    -> (mapTyCon, k', k)
            Uncurry -> (mapApplyTyCon, k, k')
#else
            Bare    -> (mapTyCon, k, k')
            Uncurry -> (mapApplyTyCon, k', k)
#endif

      in mkTyConApp con [lKind, rKind, go f, go xs]
    go (Length k x) =
      mkTyConApp lengthTyCon [k, go x]
    go (SortByAux k cmp n xs) =
      mkTyConApp sortByAuxTyCon
        [k, go cmp, go n, go xs]
    go (LookupWithIndexOM k v l dic) =
      mkTyConApp lookupWithIdxTyCon
        [k, v, go l, go dic]
    go (Lookup'OM k v l dic) =
      mkTyConApp omLookup'TyCon
        [ k, v, go l, go dic]
    go (Indexed k xs) =
      mkTyConApp indexedTyCon
        [k, go xs]
    go (Apply Uncurry f x) =
      let l = go f
          r = go x
          (dom, ran) = domRanKind Uncurry l
#if MIN_VERSION_ghc(8,8,1)
      in mkTyConApp applyTyCon [dom, ran, l, r]
#else
      in mkTyConApp applyTyCon [ran, dom, l, r]
#endif

    go (Apply Bare f x) =
      mkAppTy (go f) (go x)
    go (FromMaybe k def may) =
      mkTyConApp fromMaybeTyCon [k, go def, go may]
    go (MapMaybeApp k k' f may) =
      mkTyConApp mapMaybeTyCon [k, k', go f, go may]
    go (EmptyList k) =
      mkTyConApp promotedNilDataCon [k]
    go (PromotedJust k v) =
      mkTyConApp promotedJustDataCon [k, go v]
    go (ToListOM k v dic) =
      mkTyConApp omToListTyCon [k, v, go dic]
    go (ToListAuxOM k v acc dic) =
      mkTyConApp omToListAuxTyCon [k, v, go acc, go dic]
    go (OMIndex k v l xs) =
      mkTyConApp omIndexTyCon [k, v, go l, go xs]
    go (Index k n xs) =
      mkTyConApp indexTyCon' [k, go n, go xs, mkTyConApp promotedNilDataCon [k]]
    go (ElemAt k n xs) =
      mkTyConApp elemAtTyCon [k, go n, go xs]
    go (Drop k n xs) =
      mkTyConApp dropTyCon [k, go n, go xs]
    go (Take k n xs) =
      mkTyConApp takeTyCon [k, go n, go xs]
    go (AppList k xs ys) =
      mkTyConApp appListTyCon [k, go xs, go ys]
    go (SizeOM k v dic) =
      mkTyConApp omSizeTyCon [k, v, go dic]
    go (UnknownTyConApp con ts) =
      mkTyConApp con $ map go ts
    go (UnknownTerm k) = k

monotoneDic :: SymbolTable -> [(TyCon, FunType)]
monotoneDic STbl{..} =
  [ (monotoneTyCon, Bare)
  , (monotoneAppTyCon, Uncurry)
  ]

mapDic :: SymbolTable -> [(TyCon, FunType)]
mapDic STbl{..} =
  [ (mapTyCon, Bare)
  , (mapApplyTyCon, Uncurry)
  ]

data SymbolTable =
  STbl
    { indexedAuxTyCon  :: TyCon
    , indexedTyCon     :: TyCon
    , lengthTyCon      :: TyCon
    , sortByTyCon      :: TyCon
    , sortByAuxTyCon   :: TyCon
    , sortedByCls      :: Class
    , sortedByAuxTyCon :: TyCon
    , sOrdTyCon :: TyCon
    , monotoneTyCon    :: TyCon
    , monotoneAppTyCon :: TyCon
    , ordMapTyCon :: TyCon
    , sOrdMapTyCon :: TyCon
    , entryCTyCon :: TyCon
    , fst1TyCon :: TyCon
    , presLenTyCon     :: TyCon
    , mapTyCon         :: TyCon
    , mapApplyTyCon    :: TyCon
    , knownNatTyCon    :: TyCon
    , compare2TyCon    :: TyCon
    , indexTyCon'      :: TyCon
    , elemAtTyCon      :: TyCon
    , applyTyCon       :: TyCon
    , dropTyCon        :: TyCon
    , takeTyCon        :: TyCon
    , appListTyCon     :: TyCon
    , allTyCon         :: TyCon
    , allDicTyCon      :: TyCon
    , reifyDicId       :: Id
    , memberTyCon      :: TyCon
    , allOMTyCon       :: TyCon
      -- key val (c :: key -> val -> Constraint) dic
    , omMemberTyCon    :: TyCon
    , omLookup'TyCon   :: TyCon
    , allOMDict'FunId  :: Id
    -- :: key val (c :: key -> val -> Constraint)
    --      (dic :: OrdMap key val) (x :: key)
    --      $dAllOM $dMember
    , omIndexTyCon     :: TyCon
    -- key val (l :: key) (OrdMap key val)
    , constsDictTyCon  :: TyCon
    , omSizeTyCon      :: TyCon
    , omToListTyCon    :: TyCon
    , omToListAuxTyCon :: TyCon
    , lookupWithIdxTyCon :: TyCon
    , lookupOMTyCon :: TyCon
    , -- | @forall {k} {val} {l :: k} {dic :: OrdMap k val}. SOrd k => ...@
      sLookupWithIndex'FunId :: Id
    , fromMaybeTyCon :: TyCon
    , -- | @forall a b. (a ~> b) -> Maybe a -> Maybe b@
      mapMaybeTyCon :: TyCon
    , elimFromMaybeC'FunId :: Id
    , maybeCTyCon :: TyCon
    , knownTyCon :: TyCon
    , sApplyClass :: Class
    , singTyCon :: TyCon
    , -- | forall {k} {a :: k}. Known @{k} a => Sing @k @Type a
      sKnownVal'FunId, elimMaybeCLookup'FunId, sFMapMaybe'FunId :: Id
    }

setupSymbolTable :: TcPluginM SymbolTable
setupSymbolTable = do
  ordMod@(Module pkgId _)
    <- lookupModule (mkModuleName "Data.TypeLevel.Ord") "elgenerics-known"
  propMod <- lookupModule (mkModuleName "Data.TypeLevel.List.Properties")
              "elgenerics-known"
  let coreMod = Module pkgId $ mkModuleName "Data.TypeLevel.List.Core"
  mapTyCon <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "Map")
  memberTyCon <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "Member")
  mapApplyTyCon <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "MapApply")
  elemAtTyCon <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "ElemAt")
  indexTyCon' <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "Index'")
  lengthTyCon <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "Length")
  knownNatTyCon <- tcLookupTyCon knownNatClassName
  indexedTyCon <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "Indexed")
  indexedAuxTyCon <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "IndexedAux")
  sortByTyCon <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "SortBy")
  sortByAuxTyCon <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "SortByAux")
  compare2TyCon <- tcLookupTyCon =<< lookupName ordMod (mkTcOcc "Compare2")
  sortedByCls <- tcLookupClass =<< lookupName ordMod (mkTcOcc "SortedBy")
  sortedByAuxTyCon <- tcLookupTyCon =<< lookupName ordMod (mkTcOcc "SortedByAux")

  presLenTyCon <- tcLookupTyCon =<< lookupName propMod (mkTcOcc "PreservesLength")
  monotoneTyCon <- tcLookupTyCon =<< lookupName propMod (mkTcOcc "Monotone")
  monotoneAppTyCon <- tcLookupTyCon =<< lookupName propMod (mkTcOcc "MonotoneApply")
  funMod <- lookupModule (mkModuleName "Data.TypeLevel.Function") "elgenerics-known"
  applyTyCon <- tcLookupTyCon =<< lookupName funMod (mkTcOcc "Apply")
  dropTyCon <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "Drop")
  takeTyCon <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "Take")
  appListTyCon <- tcLookupTyCon =<< lookupName coreMod (mkTcOcc "++")
  cnstrMod <- lookupModule (mkModuleName "Data.Constraint.Operators") "elgenerics-known"
  allTyCon <- tcLookupTyCon =<< lookupName cnstrMod (mkTcOcc "All")
  allDicTyCon <- tcLookupTyCon =<< lookupName cnstrMod (mkTcOcc "AllDict")
  reifyDicId <- tcLookupId =<< lookupName cnstrMod (mkVarOcc "reifyDict")

  omMod <- lookupModule (mkModuleName "Data.TypeLevel.OrdMap") "elgenerics-known"
  allOMTyCon <- tcLookupTyCon =<< lookupName omMod (mkTcOcc "AllOM")
  omMemberTyCon <- tcLookupTyCon =<< lookupName omMod (mkTcOcc "Member")
  allOMDict'FunId <- tcLookupId =<< lookupName omMod (mkVarOcc "allOMDict'")
  omIndexTyCon <- tcLookupTyCon =<< lookupName omMod (mkTcOcc "Index")
  sLookupWithIndex'FunId <- tcLookupId =<< lookupName omMod (mkVarOcc "sLookupWithIndex'")

  constsDictTyCon <-
    tcLookupTyCon =<< lookupName cnstrMod (mkTcOcc "CustomDict")
  omLookup'TyCon <-
    tcLookupTyCon =<< lookupName omMod (mkTcOcc "Lookup'")
  omSizeTyCon <-
    tcLookupTyCon =<< lookupName omMod (mkTcOcc "Size")
  omToListTyCon <-
    tcLookupTyCon =<< lookupName omMod (mkTcOcc "ToList")
  omToListAuxTyCon <-
    tcLookupTyCon =<< lookupName omMod (mkTcOcc "ToListAux")
  lookupWithIdxTyCon <-
    tcLookupTyCon =<< lookupName omMod (mkTcOcc "LookupWithIndex")
  lookupOMTyCon <-
    tcLookupTyCon =<< lookupName omMod (mkTcOcc "Lookup")

  elimFromMaybeC'FunId <- tcLookupId =<< lookupName cnstrMod (mkVarOcc "elimFromMaybeC'")
  tyMaybeMod <- lookupModule (mkModuleName "Data.TypeLevel.Maybe") "elgenerics-known"
  fromMaybeTyCon <- tcLookupTyCon=<< lookupName tyMaybeMod (mkTcOcc "FromMaybe")
  let appMod = Module pkgId $ mkModuleName "Data.TypeLevel.Applicative"
  mapMaybeTyCon <- tcLookupTyCon=<< lookupName appMod (mkTcOcc "MapMaybe")
  sFMapMaybe'FunId <- tcLookupId =<< lookupName appMod (mkVarOcc "sFMapMaybe'")
  maybeCTyCon <- tcLookupTyCon=<< lookupName cnstrMod (mkTcOcc "MaybeC")
  let knownCoreMod = tyMaybeMod { GHC.Plugins.moduleName = mkModuleName "Data.TypeLevel.Known.Core" }
  fst1TyCon <- tcLookupTyCon =<< lookupName knownCoreMod (mkTcOcc "Fst1")
  knownTyCon <- tcLookupTyCon =<< lookupName knownCoreMod (mkTcOcc "Known")
  sKnownVal'FunId <- tcLookupId =<< lookupName knownCoreMod (mkVarOcc "sKnownVal'")
  let omIntMod  = tyMaybeMod { GHC.Plugins.moduleName = mkModuleName "Data.TypeLevel.OrdMap.Internal" }
  sOrdMapTyCon <- tcLookupTyCon =<< lookupName omIntMod (mkTcOcc "SOrdMap")
  ordMapTyCon <- tcLookupTyCon =<< lookupName omIntMod (mkTcOcc "OrdMap")
  singTyCon <- tcLookupTyCon =<< lookupName knownCoreMod (mkTcOcc "Sing")
  sOrdTyCon <- tcLookupTyCon =<< lookupName ordMod (mkTcOcc "SOrd")
  sApplyClass <- tcLookupClass =<< lookupName knownCoreMod (mkTcOcc "SApply")
  entryCTyCon <- tcLookupTyCon =<< lookupName omMod (mkTcOcc "EntryC")
  elimMaybeCLookup'FunId <- tcLookupId =<< lookupName omMod (mkVarOcc "elimMaybeCLookup'")
  return STbl{..}

infixr 0 -->, ~>
(-->), (~>) :: Type -> Type -> Type
#if MIN_VERSION_ghc(9,0,1)
(-->) = mkFunTy VisArg Many
#else
(-->) = mkFunTy VisArg
#endif
a ~> b = a --> b --> liftedTypeKind

listTy :: Type -> Type -- a |-> [a]
listTy = mkTyConApp listTyCon . pure

isUnknownC :: Constr -> Bool
isUnknownC UnknownC{} = True
isUnknownC _          = False

isUnknownTerm :: Term -> Bool
isUnknownTerm UnknownTerm{} = True
isUnknownTerm _             = False

splitFunTy' :: Type -> (Type, Type)
#if MIN_VERSION_ghc(9,0,1)
splitFunTy' = splitFunTy >>> \case
  (_, l, r) -> (l,r)
#else
splitFunTy' = splitFunTy
#endif


domRanKind :: FunType -> Type -> (Kind, Kind)
domRanKind Bare = splitFunTy' . typeKind
domRanKind Uncurry = \t ->
  let (dom, ranStar) = splitFunTy' $ typeKind t
  in (dom, fst $ splitFunTy' ranStar)

substTerm :: SymbolTable -> [(TcTyVar, Type)] -> Term -> Term
substTerm stbl subs =
  toTerm stbl . substType subs . fromTerm stbl

data WithCtLoc a = WithCtLoc { loc :: CtLoc, value :: a }
  deriving (Foldable)

instance Eq a => Eq (WithCtLoc a) where
  (==) = (==) `on` value
  (/=) = (/=) `on` value

instance Ord a => Ord (WithCtLoc a) where
  (<=) = (<=) `on` value
  (>=) = (>=) `on` value
  (<) = (<) `on` value
  (>) = (>) `on` value
  compare = compare `on` value
