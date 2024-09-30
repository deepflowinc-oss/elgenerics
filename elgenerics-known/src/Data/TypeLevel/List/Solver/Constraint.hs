{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module Data.TypeLevel.List.Solver.Constraint where

import Control.Applicative
import Control.Monad
import Data.Foldable (foldl')
import Data.Foldable qualified as F
import Data.Functor
import Data.IORef
import Data.Map.Strict qualified as M
import Data.Maybe (mapMaybe)
import Data.Set qualified as S
import Data.TypeLevel.List.Solver.Free
import Data.TypeLevel.List.Solver.Reduce
import Data.TypeLevel.List.Solver.Syntax
import Data.TypeLevel.List.Solver.Utils
import GHC.Stack
import GHC.TcPluginM.Extra
#if MIN_VERSION_ghc(9,0,1)
import GHC.Core.Class (Class (classTyCon))
import GHC.Tc.Types.Constraint
import GHC.Plugins hiding ((<>))
import GHC.Core.Predicate
import GHC.Tc.Types.Evidence
import GHC.Tc.Plugin hiding (newGiven, newWanted)
import GHC.Types.Id.Make
#else
import Class (Class (classTyCon))
import Constraint
import GhcPlugins hiding ((<>))
import MkId (proxyHashId)
import Predicate
import TcEvidence
import TcPluginM hiding (newGiven, newWanted)
#endif

-- type EvidenceDic = Map WType CtEvidence

solveConstr ::
  [(TcTyVar, Type)] ->
  SymbolTable ->
  IORef EvidenceDic ->
  IORef Normalisation ->
  [Ct] ->
  Ct ->
  TcPluginM (Maybe ((Witness, Ct), [Ct]))
solveConstr subs stbl evDicRef norms givens ct = do
  let p = ctPred $ substCt subs ct
      cnstr = toConstr stbl p
  mresl <- runSolveMode subs stbl evDicRef norms givens ct (doSolve' cnstr)
  return (mresl <&> \(a, cts) -> ((a, ct), cts))

sortMonotone ::
  (HasCallStack) =>
  FunType ->
  Kind -> -- Domain Kind
  Kind -> -- Codomain Kind
  Term -> -- (Un)curried Function
  Term -> -- Compare on Domain
  Term -> -- Compare on Codomain
  Term -> -- Target list
  Term -> -- LHS
  Term -> -- RHS
  Solver Witness
sortMonotone b dom cod h cmpDom cmpCod _ lhs rhs = do
  void $ require $ Monotone b dom cod h cmpDom cmpCod
  tbl <- getSymbolTable
  return $ evCoercion $ trustMeNominal (fromTerm tbl lhs) (fromTerm tbl rhs)

decompInnerMember ::
  Constr -> Maybe (IsWrapped, Maybe FunType, Kind, Term, Term)
decompInnerMember
  (Member b _ (Apply fTy h' x) (Map _ k _ h xs))
    | h' == h = return (b, Just fTy, k, x, xs)
decompInnerMember
  ( Member
      b
      _
      (UnknownTyConApp con args)
      (Map _ k _ (UnknownTyConApp con' args') xs)
    )
    | con == con' && init args == args' = do
        let mb = case tyConInjectivityInfo con of
              Injective bs | last bs -> Just Bare
              _ | isDataFamilyTyCon con || isDataTyCon con -> Just Bare
              _ -> Nothing
        return (b, mb, k, last args, xs)
decompInnerMember _ = Nothing

sing :: Type -> Term -> Solver EvExpr
sing a x = do
  stbl@STbl {..} <- getSymbolTable
  knownX <- require $ Known a x
  let xTy = fromTerm stbl x
      theSing =
        foldl1'
          App
          [ Var sKnownVal'FunId
          , Type a
          , Type xTy
          , dictExpr knownX
          ]
  pure theSing

mkLocalVar' :: IdDetails -> Name -> Type -> IdInfo -> Id
#if MIN_VERSION_ghc(9,0,1)
mkLocalVar' idflab nam = mkLocalVar idflab nam Many
#else
mkLocalVar' = mkLocalVar
#endif

doSolve' :: (HasCallStack) => Constr -> Solver Witness
doSolve'
  ( EqType
      NomEq
      l@(Map b k k' h (SortByAux _ cmp _ xs))
      r@(SortByAux _ cmp' _ (Map b' _ _ h' xs'))
    )
    | h == h' && xs == xs' && b == b' =
        sortMonotone b k k' h cmp cmp' xs l r
doSolve'
  ( EqType
      NomEq
      l@(SortByAux _ cmp' _ (Map b' _ _ h' xs'))
      r@(Map b k k' h (SortByAux _ cmp _ xs))
    )
    | h == h' && xs == xs' && b == b' =
        sortMonotone b k k' h cmp cmp' xs l r
doSolve' (EqType NomEq l r) = do
  stbl <- getSymbolTable
  let (l', r') = (reduce l, reduce r)
  guard
    ( not $
        fromTerm stbl l
          `eqType` fromTerm stbl l'
          && fromTerm stbl r
            `eqType` fromTerm stbl r'
    )
  unless (l' == r') $
    void $
      require (EqType NomEq l' r')
  return $ evCoercion $ trustMeNominal (fromTerm stbl l) (fromTerm stbl r)
doSolve' (decompInnerMember -> Just (b, _, k, x, xs)) =
  unsafeDicToWitnessM =<< require (Member b k x xs)
doSolve' (Member _ _ (ElemAt _ n xs) xs') | xs == xs' = do
  unsafeDicToWitnessM =<< require (KnownNat n)
doSolve' (KnownNat (Length k inner)) =
  case inner of
    Map _ a _ _ xs ->
      unsafeDicToWitnessM =<< require (KnownNat (Length a xs))
    SortByAux _ _ _ xs ->
      unsafeDicToWitnessM =<< require (KnownNat (Length k xs))
    Indexed k' xs ->
      unsafeDicToWitnessM =<< require (KnownNat (Length k' xs))
    _ -> mzero
doSolve' (SortedBy k cmp (SortByAux _ cmp' _ _)) | cmp == cmp' = do
  unsafeDicToWitnessM =<< require (SortedBy k cmp (EmptyList k))
doSolve' (SortedBy k cmp (Map fty a _ h xs)) = do
  let cmp2 = Compare2 a
  void $ require $ Monotone fty a k h cmp2 cmp
  unsafeDicToWitnessM =<< require (SortedBy a cmp2 xs)
doSolve' cwhole@(MaybeC _v' c (MapMaybeApp _ _v'' t (LookupWithIndexOM k v l dic))) = do
  stbl@STbl {..} <- getSymbolTable
  let fTy = fromTerm stbl t
      instHead = fromConstr stbl cwhole
  case splitTyConApp_maybe fTy of
    Just (con, _) | con == fst1TyCon -> do
      let cTy = fromTerm stbl c
          lTy = fromTerm stbl l
          dicTy = fromTerm stbl dic
      knownL <- require $ Known k l
      allOMDic <-
        require $
          AllOM
            k
            v
            (UnknownTerm $ mkTyConApp entryCTyCon [k, v, cTy])
            dic
      let mkDicDataCon = tyConSingleDataCon constsDictTyCon
          cDictGoal = mkTyConApp constsDictTyCon [instHead]
          cDictLookup =
            mkTyConApp
              constsDictTyCon
              [ fromConstr stbl $
                  MaybeC _v' c (UnknownTyConApp lookupOMTyCon [UnknownTerm k, UnknownTerm v, l, dic])
              ]
      sOrdDic <- require $ UnknownC $ mkTyConApp sOrdTyCon [k]
      let getter =
            foldl1'
              App
              [ Var elimMaybeCLookup'FunId
              , Type k
              , Type v
              , Type cTy
              , Type lTy
              , Type dicTy
              , dictExpr sOrdDic
              , dictExpr knownL
              , dictExpr allOMDic
              ]
              `Cast` trustMe'
                "doSolve'/MaybeC(Lookup)"
                cDictLookup
                cDictGoal
      uq <- liftTcPluginM newUnique
      let nam = mkInternalName uq (mkVarOcc "$fs") noSrcSpan
          var = mkLocalVar' VanillaId nam cDictGoal vanillaIdInfo
      dicVar <- liftTcPluginM $ newEvVar instHead
      pure $
        EvExpr $
          Case
            getter
            var
            instHead
            [Alt (DataAlt mkDicDataCon) [dicVar] $ Var dicVar]
    _ -> doSolve' $ UnknownC $ fromConstr stbl cwhole
doSolve' knwn@(Known mb e@(MapMaybeApp a b f x)) = do
  tbl@STbl {..} <- getSymbolTable
  let fTy = fromTerm tbl f
      xTy = fromTerm tbl x
      instHead = fromConstr tbl knwn
      eTy = fromTerm tbl e
  singX <- sing (mkTyConApp maybeTyCon [a]) x
  sApplyFDic <- require $ UnknownC $ mkTyConApp (classTyCon sApplyClass) [a, b, fTy]
  let theSing =
        foldl1'
          App
          [ Var sFMapMaybe'FunId
          , Type a
          , Type b
          , Type fTy
          , Type xTy
          , dictExpr sApplyFDic
          , foldl1' App [Var proxyHashId, Type (a ~> b), Type fTy]
          , singX
          ]
          `Cast` trustMe' "doSolve'/MapMaybe" (mkTyConApp singTyCon [mb, eTy]) instHead
  pure $ EvExpr theSing
doSolve' knownLWI@(Known may lwi@(LookupWithIndexOM k v l dic)) = do
  tbl@STbl {..} <- getSymbolTable
  let lTy = fromTerm tbl l
      ordMapTy = mkTyConApp ordMapTyCon [k, v]
      lwiE = fromTerm tbl lwi
      dicTy = fromTerm tbl dic
      instHead = fromConstr tbl knownLWI
  lSing <- sing k l
  dicSing <- sing ordMapTy dic
  sordDic <- require $ UnknownC $ mkTyConApp sOrdTyCon [k]
  let looked =
        foldl1'
          App
          [ Var sLookupWithIndex'FunId
          , Type k
          , Type v
          , Type lTy
          , Type dicTy
          , dictExpr sordDic
          , lSing
          , dicSing
          ]
          `Cast` trustMe'
            "doSolve'/KnownLWI"
            (mkTyConApp singTyCon [may, lwiE])
            instHead
  pure $ EvExpr looked
doSolve' (KnownTyList _ inner) = do
  mdecons <- deconsKTL inner
  case mdecons of
    InnerList k' as ->
      unsafeDicToWitnessM =<< require (KnownTyList k' as)
    InnerOrdMap k v dic ->
      unsafeDicToWitnessM =<< require (KnownNat (SizeOM k v dic))
doSolve' c = do
  tbl <- getSymbolTable
  givens <- getGivens
  let prd = fromConstr tbl c
  case splitAppTys prd of
    (cnstr, args)
      | not (null args)
      , let targ = toTerm tbl $ last args
      , FromMaybe k def may <- targ ->
          solveFromMaybeC (foldl' mkAppTy cnstr $ init args) k def may
    _ -> do
      Just (clsHead, targ) <-
        return $
          do
            (cls, args) <- getClassPredTys_maybe prd
            guard $ not $ null args
            let (hdr, targ) = head <$> splitAt (length args - 1) args
                clsHead = mkClassPred cls hdr
            return (clsHead, targ)
            <|> do
              (con, args) <- splitTyConApp_maybe prd
              guard $ not $ null args
              let (hdr, targ) = head <$> splitAt (length args - 1) args
                  clsHead = mkTyConApp con hdr
              return (clsHead, targ)
            <|> splitAppTy_maybe prd

      amd : _ <-
        return $
          findAllMembers tbl (toTerm tbl clsHead) (toTerm tbl targ) givens
      EvExpr <$> generateDicFromAll amd

solveFromMaybeC :: Type -> Kind -> Term -> Term -> Solver Witness
solveFromMaybeC c k def may = do
  stbl <- getSymbolTable
  let instHead = c `mkAppTy` fromTerm stbl (FromMaybe k def may)
  maybeCDic <- require (MaybeC k (UnknownTerm c) may)
  defDic <- require (UnknownC $ c `mkAppTy` fromTerm stbl def)
  knownDic <- require $ Known (mkTyConApp maybeTyCon [k]) may
  let getter =
        foldl1
          App
          [ Var $ elimFromMaybeC'FunId stbl
          , Type k
          , Type c
          , Type $ fromTerm stbl def
          , Type $ fromTerm stbl may
          , dictExpr defDic
          , dictExpr maybeCDic
          , dictExpr knownDic
          ]
  uq <- liftTcPluginM newUnique
  let mkDicDataCon = tyConSingleDataCon $ constsDictTyCon stbl
      nam = mkInternalName uq (mkVarOcc "$fs") noSrcSpan
      v = mkLocalVar' VanillaId nam (mkTyConApp (constsDictTyCon stbl) [instHead]) vanillaIdInfo
  dicVar <- liftTcPluginM $ newEvVar instHead
  pure $
    EvExpr $
      Case
        getter
        v
        instHead
        [Alt (DataAlt mkDicDataCon) [dicVar] $ Var dicVar]

generateDicFromAll :: AllMemberDic -> Solver EvExpr
generateDicFromAll AllMemberDic {..} = do
  tbl@STbl {..} <- getSymbolTable
  let chd = fromTerm tbl classHead
      x = fromTerm tbl element
      k = typeKind x
  uq <- liftTcPluginM newUnique
  let instHead = chd `mkAppTy` x
  dicVar <- liftTcPluginM $ newEvVar instHead
  let nam = mkInternalName uq (mkVarOcc "$fs") noSrcSpan
      xs = fromTerm tbl superList
      concDicType = mkTyConApp allDicTyCon [k, chd, x, xs]
      v = mkLocalVar' VanillaId nam concDicType vanillaIdInfo
      getter =
        foldl1
          App
          [ Var reifyDicId
          , Type k
          , Type chd
          , Type x
          , Type xs
          , memberDic
          , allDic
          ]
  let mkDicDataCon = tyConSingleDataCon allDicTyCon
  return $
    Case
      getter
      v
      instHead
      [Alt (DataAlt mkDicDataCon) [dicVar] $ Var dicVar]

generateDicFromAllOM ::
  -- | key kind
  Kind ->
  -- | val kind
  Kind ->
  -- | Lookup' x dic
  Type ->
  AllMemberDic ->
  Solver EvExpr
generateDicFromAllOM
  key
  val
  lookuped
  AllMemberDic {..} = do
    tbl@STbl {..} <- getSymbolTable
    let chd = fromTerm tbl classHead
        xs = fromTerm tbl superList
        x = fromTerm tbl element
    uq <- liftTcPluginM newUnique
    liftTcPluginM $
      tcPluginTrace "LIST: instheads" $
        ppr ((chd, typeKind chd), (x, typeKind x), (lookuped, typeKind lookuped))
    let instHead = instBinaryPred chd x lookuped
        nam = mkInternalName uq (mkVarOcc "$fsOMAllMemDecons") noSrcSpan
        concDicType = mkTyConApp constsDictTyCon [oldInstHead]
        oldLooked = fromTerm tbl $ Lookup'OM key val element superList
        oldInstHead = (chd `mkAppTy` x) `mkAppTy` oldLooked
        v = mkLocalVar' VanillaId nam concDicType vanillaIdInfo
        getter =
          foldl1
            App
            [ Var allOMDict'FunId
            , Type key
            , Type val
            , Type chd
            , Type xs
            , Type x
            , allDic
            , memberDic
            ]
    let mkDicDataCon = tyConSingleDataCon constsDictTyCon
    dicVar <- liftTcPluginM $ newEvVar oldInstHead
    return $
      Case
        getter
        v
        instHead
        [ Alt
            (DataAlt mkDicDataCon)
            [dicVar]
            $ Var dicVar
              `Cast` trustMe' "generateDicFromAllOM" oldInstHead instHead
        ]

instBinaryPred :: Type -> Type -> Type -> Type
instBinaryPred clsHead lab val =
  mkAppTys clsHead [lab, val]

data DecomposedKnownTyList
  = InnerList {elKind :: Kind, innerTerm :: Term}
  | InnerOrdMap {dKeyKind :: Kind, dValKind :: Kind, innerTerm :: Term}

deconsKTL :: Term -> Solver DecomposedKnownTyList
deconsKTL = deconsListTerm False

deconsMember :: Term -> Solver DecomposedKnownTyList
deconsMember = deconsListTerm True

deconsListTerm ::
  -- | 単射の場合のみ同一視するか？
  Bool ->
  Term ->
  Solver DecomposedKnownTyList
deconsListTerm _ (SortByAux k _ _ xs) = return $ InnerList k xs
deconsListTerm False (Map _ a _ _ xs) = return $ InnerList a xs
deconsListTerm True (Map Bare a _ _ xs) = return $ InnerList a xs
deconsListTerm _ (Indexed k xs) = return $ InnerList k xs
deconsListTerm _ (ToListOM k v dic) = do
  return $ InnerOrdMap k v dic
deconsListTerm _ (ToListAuxOM k v EmptyList {} dic) = do
  return $ InnerOrdMap k v dic
deconsListTerm _ (UnknownTerm ty)
  | Just (con, args) <- splitTyConApp_maybe ty
  , not (null args) = do
      let xs = last args
          k' = typeKindElem xs
      void $
        require $
          PreservesLength (UnknownTerm $ mkTyConApp con (init args))
      return $ InnerList k' (UnknownTerm xs)
deconsListTerm _ _ = mzero

data AllMemberDic = AllMemberDic
  { classHead :: Term
  , superList :: Term
  , element :: Term
  , memberDic :: CoreExpr
  , isMemberWrapped :: IsWrapped
  , allDic :: CoreExpr
  }

findAllMembers ::
  SymbolTable ->
  -- | Class tycon
  Term ->
  -- | Target term
  Term ->
  -- | Constraint
  Givens ->
  [AllMemberDic]
findAllMembers senv@STbl {} clsType targ cDic =
  let kind = typeKind $ fromTerm senv targ
      (mems, alls) =
        M.foldMapWithKey
          ( \c ct -> case c of
              Member b _ x xs
                | x == targ -> (M.singleton xs (b, ct), M.empty)
              All k cns xs
                | cns == clsType
                , k `eqType` kind ->
                    (M.empty, M.singleton xs ct)
              _ -> mempty
          )
          cDic
      targKey =
        M.keysSet mems `S.intersection` M.keysSet alls
   in [ AllMemberDic
        { classHead = clsType
        , superList = xs
        , element = targ
        , memberDic = buildMemDic senv targ xs $ snd $ mems M.! xs
        , isMemberWrapped = fst $ mems M.! xs
        , allDic = ctEvExpr $ alls M.! xs
        }
      | xs <- S.toList targKey
      ]

{-
-- List の場合と異なり、(Member v xs) から c v (Lookup' v xs)
-- までしか言えず、c v x を解決する際には (x ~ Lookup' v xs)
-- が必要になる。どうするか考えものなので、ちょっと考える。
findAllOMMembers
  :: SymbolTable
  -> Term  -- ^ Class tycon
  -> Term  -- ^ Target key term
  -> Term  -- ^ Target value term
  -> Givens -- ^ Constraint
  -> [(Kind, Kind, AllMemberDic)]
-}
decompOMAlls ::
  Solver [Ct]
decompOMAlls = do
  givens <- getGivens
  tbl <- getSymbolTable

  let kns =
        M.mapKeysMonotonic
          ( \case
              KnownNat n -> n
              _ -> error "Could not happen!"
          )
          $ M.filterWithKey
            ( \case
                KnownNat {} -> const True
                _ -> const False
            )
            givens
  let alls =
        [ ( k
          , v
          , l
          , AllMemberDic
              { classHead = c
              , superList = xs
              , element = x
              , memberDic = buildMemOMDic tbl k v x xs memD
              , isMemberWrapped = True
              , allDic = ctEvExpr allD
              }
          , ctev_loc allD
          )
        | (AllOM k v c xs, allD) <- M.toList givens
        , let dic =
                M.fromListWith (<>) $
                  map (\elkey -> (omLabel elkey, elkey)) $
                    mapMaybe (uncurry $ decompOMMember kns k v xs) $
                      M.toList givens
        , elKeyDics <- F.toList dic
        , let (x, l, memD) = (omLabel elKeyDics, omValue elKeyDics, omDic elKeyDics)
        ]
  forM alls $ \(k, v, l, amd@AllMemberDic {..}, loc) -> do
    let c = fromTerm tbl classHead
        x = fromTerm tbl element
    let lookedup = fromTerm tbl l
        prd =
          foldl1'
            mkAppTy
            [c, x, lookedup]
    ev <- EvExpr <$> generateDicFromAllOM k v lookedup amd
    mkNonCanonical' loc <$> liftTcPluginM (newGiven loc prd ev)

decompAlls ::
  Solver [Ct]
decompAlls = do
  givens <- getGivens
  tbl <- getSymbolTable
  let alls =
        [ ( fromTerm tbl c `mkAppTy` fromTerm tbl x
          , AllMemberDic
              { classHead = c
              , superList = xs
              , element = x
              , memberDic = buildMemDic tbl x xs memD
              , isMemberWrapped = b
              , allDic = ctEvExpr allD
              }
          , ctev_loc allD
          )
        | (All k c xs, allD) <- M.toList givens
        , (Member b _ x _, memD) <-
            filter (isMemberOfC k xs . fst) $
              M.toList givens
        ]
  forM alls $ \(prd, amd, loc) -> do
    ev <- EvExpr <$> generateDicFromAll amd
    mkNonCanonical' loc <$> liftTcPluginM (newGiven loc prd ev)

isMemberOfC ::
  Kind -> Term -> Constr -> Bool
isMemberOfC k xs (Member _ k' _ ys)
  | xs == ys && k `eqType` k' = True
isMemberOfC _ _ _ = False

data OMElemKey
  = OMDefiniteElemKey {omLabel :: Term, omValue :: Term, omDic :: CtEvidence}
  | OMDynamicElemKey {omLabel :: Term, omValue :: Term, omDic :: CtEvidence}

type KnownNats = M.Map Term CtEvidence

instance Semigroup OMElemKey where
  l@OMDefiniteElemKey {} <> _ = l
  OMDynamicElemKey {} <> r@OMDefiniteElemKey {} = r
  l@OMDynamicElemKey {} <> OMDynamicElemKey {} = l

decompOMMember ::
  KnownNats -> Kind -> Kind -> Term -> Constr -> CtEvidence -> Maybe OMElemKey
decompOMMember
  kns
  k
  v
  xs
  ( EqType
      NomEq
      (LookupWithIndexOM k' v' l ys)
      (PromotedJust _ (PromotedTuple _ _ value n))
    )
  _
    | Just dic <- M.lookup n kns
    , xs == ys
    , k `eqType` k'
    , eqType v v' =
        Just $ OMDefiniteElemKey l value dic
decompOMMember _ k v xs (MemberOM _ k' v' l ys) dic
  | xs == ys && k `eqType` k' && eqType v v' =
      Just $ OMDynamicElemKey l (Lookup'OM k' v' l ys) dic
decompOMMember _ _ _ _ _ _ = Nothing

buildMemDic ::
  SymbolTable -> Term -> Term -> CtEvidence -> CoreExpr
buildMemDic stbl x xs ctev =
  let k = typeKind $ fromTerm stbl x
      memTy = fromConstr stbl (Member True k x xs)
   in ctEvExpr ctev `Cast` trustMe' "walkMemPath" (ctEvPred ctev) memTy

buildMemOMDic ::
  SymbolTable -> Kind -> Kind -> Term -> Term -> CtEvidence -> CoreExpr
buildMemOMDic stbl key val x xs ctev =
  let memTy = fromConstr stbl (MemberOM True key val x xs)
   in ctEvExpr ctev `Cast` trustMe' "buildMemOMDic" (ctEvPred ctev) memTy
