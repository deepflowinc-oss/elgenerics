{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module Data.TypeLevel.List.Solver.Generation where

import Control.Applicative
import Control.Lens
import Control.Monad
import Control.Monad.ST
import Data.Coerce
import Data.DList qualified as DL
import Data.Foldable as F
import Data.Function
import Data.IORef
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe
import Data.Monoid hiding (All, First)
import Data.Ord
import Data.Primitive
import Data.Semigroup (First (..))
import Data.Set qualified as S
import Data.TypeLevel.List.Solver.Constraint
import Data.TypeLevel.List.Solver.Free
import Data.TypeLevel.List.Solver.Reduce
import Data.TypeLevel.List.Solver.Syntax
import Data.TypeLevel.List.Solver.Utils
import Data.UnionFind.Primitive
import GHC.TcPluginM.Extra
#if MIN_VERSION_ghc(9,0,1)
import GHC.Tc.Types.Constraint
import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Predicate
import GHC.Tc.Types.Evidence
import GHC.Tc.Plugin hiding (newGiven, newWanted)
#else
import Constraint
import GhcPlugins hiding (empty, (<>))
import Predicate
import TcEvidence
import TcPluginM hiding (newGiven, newWanted)
#endif

classifySubExprM ::
  (Ord a, Plated a, PrimMonad m) =>
  (a -> m (Maybe a)) ->
  MutVar (PrimState m) (Map a (Point m a)) ->
  a ->
  m ()
classifySubExprM decomp dicRef = mapMOf_ cosmos go
  where
    {-# INLINE getPt #-}
    getPt t = do
      dic <- readMutVar dicRef
      case M.lookup t dic of
        Nothing -> do
          v <- fresh t
          modifyMutVar' dicRef $ M.insert t v
          return v
        Just v -> return v
    go t = do
      s <- decomp t
      forM_ s $ \sub -> do
        tPt <- getPt t
        subPt <- getPt sub
        union tPt subPt

-- | /O(m*log(n/m + 1)), m <= n/ で mappend できる
newtype CatMap k v = CatMap {runCatMap :: Map k v}
  deriving (Read, Show, Eq, Ord)

instance
  (Ord k, Semigroup v) =>
  Semigroup (CatMap k v)
  where
  (<>) = coerce $ M.unionWith @k @v (<>)
  {-# INLINE (<>) #-}

instance
  (Ord k, Semigroup v) =>
  Monoid (CatMap k v)
  where
  mempty = CatMap M.empty

generateDecompConstr ::
  (Foldable t) =>
  (Term -> Solver Term) ->
  (SymbolTable -> Term -> Constr) ->
  t Term ->
  Solver (Map Constr Ct)
generateDecompConstr decomp toC ts = do
  dics <-
    filter (not . null)
      <$> classifyByM (optional . decomp) ts
  fold . catMaybes <$> mapM (optional . shareDictsAmong toC) dics

generateKnownTyLists ::
  [Term] ->
  Solver (Map Constr Ct)
generateKnownTyLists =
  generateDecompConstr (fmap innerTerm . deconsKTL) $ \stbl xs ->
    KnownTyList (typeKindElem $ fromTerm stbl xs) xs

shareDictsAmong ::
  (SymbolTable -> Term -> Constr) ->
  [Term] ->
  Solver (Map Constr Ct)
shareDictsAmong cls ts = do
  stbl <- getSymbolTable
  (orig, dic) <-
    asum
      [ (xs,) <$> require (cls stbl xs)
      | xs <- ts
      ]
  fmap M.fromList $
    forM (filter (/= orig) ts) $ \xs ->
      let p = cls stbl xs
       in fmap ((p,) . mkNonCanonical)
            . liftTcPluginM
            . newGiven (dictLoc dic) (fromConstr stbl p)
            =<< unsafeDicToWitnessFor (Right p) dic

classifyByM ::
  (Foldable t, Syntax s, PrimMonad m) =>
  (Term' s -> m (Maybe (Term' s))) ->
  t (Term' s) ->
  m [[Term' s]]
classifyByM decomp terms = do
  dicRef <- newMutVar M.empty
  mapM_ (classifySubExprM decomp dicRef) terms
  dic <- readMutVar dicRef
  fmap (M.elems . fmap DL.toList . runCatMap) $
    getAp $
      M.foldMapWithKey
        ( \k pt ->
            CatMap . flip M.singleton (DL.singleton k)
              <$> Ap (descriptor =<< repr pt)
        )
        dic

classifyBy ::
  (Foldable t, Syntax s) =>
  (Term' s -> Maybe (Term' s)) ->
  t (Term' s) ->
  [[Term' s]]
classifyBy f xs = runST $ classifyByM (return . f) xs

data MemBuilder = BuildMem {mbList :: Term, mkWrap :: (FunType, Term)}

instance Eq MemBuilder where
  (==) = (==) `on` mbList

instance Ord MemBuilder where
  compare = comparing mbList

instance Show MemBuilder where
  showsPrec d (BuildMem p b) =
    showParen (d > 10) $
      showString "BuildMem " . showsPrec 11 p . showsPrec 11 b

type MemPath = [MemBuilder]

walkMemPath ::
  Dictionary -> Term -> MemPath -> Solver (Map Constr Dictionary)
walkMemPath dic0 x0 pth = do
  fmap (foldMap $ \(_, p, r) -> M.singleton p r) $
    sequence $
      init $
        scanr go (return (x0, undefined, dic0)) pth
  where
    go (BuildMem lst wrapElem) mkXDic = do
      (x, _, dic) <- mkXDic
      stbl <- getSymbolTable
      let hx = uncurry Apply wrapElem x
          p = Member False (typeKind $ fromTerm stbl hx) hx lst
          mem = fromConstr stbl p
          dic' = castDicTo dic mem
      return (hx, p, dic')

castDicTo :: Dictionary -> PredType -> Dictionary
castDicTo dic p =
  dic
    { dictPred = p
    , dictExpr =
        dictExpr dic
          `Cast` trustMe' "walkMemPath" (dictPred dic) p
    }

generateMembers ::
  (Foldable t) =>
  t Term ->
  Solver (Map Constr Ct)
generateMembers targs = do
  gs <- getGivens
  stbl <- getSymbolTable
  let paths = buildMemPaths targs
      mems =
        [ (dic, x, ps)
        | ((Member _ _ x xs), dic) <-
            M.toList $ fmap ctEvToDictionary gs `M.union` mems'
        , Just ps <- return $ M.lookup xs paths
        ]
      mems' = decompInjMember stbl gs
  getAp $
    foldMap
      ( \(dic, x, ps) ->
          foldMap (Ap . (mapM dicToGivenCt <=< walkMemPath dic x)) ps
      )
      mems

dicToGivenCt ::
  Dictionary -> Solver Ct
dicToGivenCt Dictionary {..} =
  liftTcPluginM $
    mkNonCanonical' dictLoc
      <$> newGiven dictLoc dictPred (EvExpr dictExpr)

buildMemPaths :: (Foldable t) => t Term -> Map Term (S.Set MemPath)
buildMemPaths = runCatMap . foldMap (CatMap . buildMemPathsFor)

buildMemPathsFor :: Term -> Map Term (S.Set MemPath)
buildMemPathsFor = runCatMap . foldMapOf cosmos go'
  where
    go' t =
      let (xs, bcs) = go t
       in CatMap $ M.singleton xs $ S.singleton bcs
    go memList@(Map' b _ _ h inner) =
      let (xs0, bcs) = go inner
          bc = BuildMem memList (b, h)
       in (xs0, bc : bcs)
    go xs = (xs, [])

generateNontrivials :: ListSolverState -> [Ct] -> TcPluginM [Ct]
generateNontrivials (LSS redRef stbl@STbl {} ref doneRef _ norms) givens = do
  tcPluginTrace "LIST: Simplification started with: " $ ppr givens
  (red0, toReduce) <- tcPluginIO $ do
    toReduce <- readIORef ref
    modifyIORef' doneRef $ S.union toReduce
    (,toReduce) <$> readIORef redRef
  let subs = map fst $ mkSubst' givens
  redex <-
    fmap (M.fromList . catMaybes)
      $ mapM
        ( \ct ->
            let p = ctPred ct
                c = toConstr stbl p
                c' = reduceC stbl c
                p' = fromConstr stbl c'
             in if c /= c' && case c of EqType {} -> False; _ -> True
                  then do
                    ct' <-
                      fmap (mkNonCanonical' (ctLoc ct)) $
                        newGiven (ctLoc ct) p' $
                          ctEvExpr (ctEvidence ct) `evCast` trustMe' "redex" p p'
                    return $ Just (c', ct')
                  else return Nothing
        )
      $ flattenGivens givens
  tcPluginTrace "LIST: redex keys" $ ppr $ show $ M.keys redex
  let presEqs =
        S.fromList $
          [ (l, r)
          | EqType NomEq l r <- map (toConstr stbl . ctPred) $ flattenGivens givens
          ]
      red = red0 `S.union` presEqs
      eqs =
        foldMap
          ( \(WithCtLoc loc foo) ->
              S.mapMonotonic (WithCtLoc loc) $
                deriveEquality red stbl foo
          )
          $ S.union toReduce
          $ S.fromList
          $ filter (not . isUnknownC . value)
          $ map
            ( WithCtLoc
                <$> ctLoc
                <*> toConstr stbl
                  . ctPred
                  . substCt subs
            )
            givens
  tcPluginIO $
    modifyIORef'
      redRef
      ((`S.union` S.map value eqs) . (`S.union` presEqs))
  dervs <- forM (S.toList eqs) $
    \(WithCtLoc loc (fromTerm stbl -> l, fromTerm stbl -> r)) ->
      mkNonCanonical' loc
        <$> newGiven
          loc
          (mkPrimEqPred l r)
          (evCoercion $ trustMeNominal l r)
  gDic <- buildGivenDic stbl norms givens
  alls <- fromMaybe [] <$> runGenerationMode stbl norms gDic decompAlls
  omAlls <- fromMaybe [] <$> runGenerationMode stbl norms gDic decompOMAlls
  let subterms =
        map (substTerm stbl subs) $
          S.toList $
            S.unions
              [ foldMap (S.fromList . F.toList . value) toReduce
              , foldMap (S.fromList . F.toList) (M.keys gDic)
              ]
      allsDic = M.fromList [(toConstr stbl $ ctPred ct, ct) | ct <- alls]
      omAllsDic = M.fromList [(toConstr stbl $ ctPred ct, ct) | ct <- omAlls]
  dones <- tcPluginIO $ readIORef doneRef
  let giveCs =
        S.fromList
          [ WithCtLoc (ctLoc ct) $
            toConstr stbl $
              ctPred ct
          | ct <- flattenGivens givens
          ]
  knownsDic <-
    fmap (fromMaybe M.empty) $
      runGenerationMode stbl norms gDic $
        generateKnownTyLists subterms
  memDic <-
    fmap (fromMaybe M.empty) $
      runGenerationMode stbl norms gDic $
        generateMembers subterms
  let genDic0 =
        M.unions
          [knownsDic, allsDic, omAllsDic, memDic, redex]
      exKeys = giveCs `S.union` dones
      genDic = genDic0 `M.withoutKeys` S.mapMonotonic value exKeys
      gens = F.toList genDic
  tcPluginIO $
    modifyIORef' doneRef $
      S.union $
        S.mapMonotonic (\k -> WithCtLoc (ctLoc $ genDic M.! k) k) $
          M.keysSet genDic
  tcPluginTrace "LIST: Derived constraints: " $ ppr $ dervs ++ gens
  return (dervs ++ gens)

decompInjMember ::
  SymbolTable -> Givens -> Map Constr Dictionary
decompInjMember stbl givens =
  maybe M.empty ((`M.withoutKeys` M.keysSet givens) . coerce . runCatMap)
    . M.foldMapWithKey go
    $ fmap ctEvToDictionary givens
  where
    go :: Constr -> Dictionary -> Maybe (CatMap Constr (First Dictionary))
    go cnstr ct = do
      (w, Just Bare, k, x, xs) <- decompInnerMember (reduceC stbl cnstr)
      let inner = Member w k (reduce x) (reduce xs)
          p' = fromConstr stbl inner
          ct' = ct `castDicTo` p'
      return (CatMap $ M.singleton inner $ First ct')
        <> go inner ct'
