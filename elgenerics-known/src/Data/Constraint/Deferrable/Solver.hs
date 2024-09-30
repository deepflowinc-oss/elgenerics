{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Constraint.Deferrable.Solver (plugin) where

import Data.Function
import Data.IORef
import Data.List (find)
import Data.Map.Strict qualified as M
import Data.Maybe
import GHC.Core.Class
import GHC.Core.Predicate
import GHC.Core.TyCo.Rep (UnivCoProvenance (PluginProv))
import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin hiding (newGiven, newWanted)
import GHC.Tc.Types (TcPlugin (..), TcPluginResult (..))
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.TcPluginM.Extra

plugin :: Plugin
plugin =
  defaultPlugin
    { tcPlugin = Just . deferrableTcPlugin
    , pluginRecompile = purePlugin
    }

deferrableTcPlugin :: [CommandLineOption] -> TcPlugin
deferrableTcPlugin opts =
  TcPlugin
    { tcPluginInit = initDeferrableState opts
    , tcPluginSolve = deferrableSolver
    , tcPluginStop = finaliseDeferrableState
    }

finaliseDeferrableState ::
  DeferrableState -> TcPluginM ()
finaliseDeferrableState DS {..} = do
  tcPluginIO $ writeIORef deferred M.empty
  pure ()

data NameTbl = NameTbl
  { _Deferrable :: Class
  , _ReifiedDeferrable :: TyCon
  , _presentDictId :: Id
  }

newtype CType = CType {runCType :: Type}

instance Eq CType where
  (==) = eqType `on` runCType

instance Ord CType where
  compare = nonDetCmpType `on` runCType

data DeferrableState = DS
  { nameTbl :: NameTbl
  , undeferOpens :: Bool
  , deferred :: IORef (M.Map CType Ct)
  }

initDeferrableState ::
  [CommandLineOption] ->
  TcPluginM DeferrableState
initDeferrableState opts = do
  deferred <- tcPluginIO $ newIORef M.empty
  constrMod <- lookupModule (mkModuleName "Data.Constraint.Deferrable") "constraints"
  opsMod <- lookupModule (mkModuleName "Data.Constraint.Operators") "elgenerics-known"
  Just _Deferrable <-
    fmap tyConClass_maybe . tcLookupTyCon
      =<< lookupName constrMod (mkTcOcc "Deferrable")
  _ReifiedDeferrable <-
    tcLookupTyCon
      =<< lookupName opsMod (mkTcOcc "ReifiedDeferrable")
  _presentDictId <-
    tcLookupId
      =<< lookupName opsMod (mkVarOcc "presentDict")
  let nameTbl = NameTbl {..}
      undeferOpens = elem "undefer-open-constraints" opts
  pure DS {..}

deferrableSolver ::
  DeferrableState ->
  [Ct] ->
  [Ct] ->
  [Ct] ->
  TcPluginM TcPluginResult
-- Reduction: geneates @Deferrable@s from
-- the given (non-deferrable) constraints.
deferrableSolver env givens [] [] = do
  defs <- deriveDeferrables env givens
  pure $ TcPluginOk [] defs

-- Solving phase:
--
-- For each @Deferrable p@, we do:
--   1. Checks if @p@ is in [G]ivens
--   2. if absent and @p@ has no free variable,
--      adds @p@ to the new [W]anteds and use it.
deferrableSolver env@DS {..} givens _ wanteds = do
  let gs' = flattenGivens givens
      subs = map fst $ mkSubst' givens
      ws' =
        mapMaybe (\o -> (o,) <$> deconsDeferrable nameTbl (ctPred $ newCt o)) $
          map (WithOrig <$> id <*> substCt subs) wanteds
  (solveds, newWants) <-
    unzip . catMaybes <$> mapM (uncurry $ trySolve env gs') ws'
  pure $ TcPluginOk solveds $ catMaybes newWants

trySolve ::
  DeferrableState ->
  [Ct] ->
  WithOrig ->
  PredType ->
  TcPluginM (Maybe ((EvTerm, Ct), Maybe Ct))
trySolve DS {nameTbl = tbl@NameTbl {}, ..} gs WithOrig {..} targPred = do
  case find ((== CType targPred) . CType . ctPred) gs of
    Just ct -> do
      let undefEv = buildUndeferred tbl targPred $ ctEvExpr $ ctEvidence ct
      pure $ Just ((undefEv, origCt), Nothing)
    _
      | noFreeVarsOfType targPred || undeferOpens -> do
          ctEv <- newWantedOrHole (ctLoc origCt) targPred
          let want = mkNonCanonical' (ctLoc origCt) ctEv
              undefEv = buildUndeferred tbl targPred $ ctEvExpr ctEv
          tcPluginIO $
            modifyIORef' deferred $
              M.insert (CType targPred) want
          pure $ Just ((undefEv, origCt), Just want)
      | otherwise -> pure Nothing

data WithOrig = WithOrig {origCt :: Ct, newCt :: Ct}

data WithCtLoc a = WithCtLoc CtLoc a
  deriving (Foldable)

buildUndeferred :: NameTbl -> Type -> CoreExpr -> EvTerm
buildUndeferred NameTbl {..} ty dict =
  EvExpr
    $ Cast
      ( Var _presentDictId
          `App` Type ty
          `App` dict
      )
    $ trustMe'
      "buildEv"
      (mkAppTy (mkTyConTy _ReifiedDeferrable) ty)
      (mkAppTy (mkTyConTy $ classTyCon _Deferrable) ty)

deriveDeferrables ::
  DeferrableState -> [Ct] -> TcPluginM [Ct]
deriveDeferrables DS {nameTbl = tbl@NameTbl {..}, ..} gs0 = do
  defs <- tcPluginIO $ readIORef deferred
  let subs = map fst $ mkSubst' gs0
      gs = flattenGivens gs0
      locConsts =
        [ WithCtLoc (ctLoc ct) (ct', p)
        | ct <- gs
        , let ct' = substCt subs ct
              p = ctPred ct'
        , CType p `M.notMember` defs
        , case classifyPredType p of
            ClassPred cls _ -> cls /= _Deferrable
            _ -> True
        ]
  cts <- mapM (buildEv tbl) locConsts
  tcPluginIO $
    modifyIORef' deferred $
      M.union
        ( M.fromList $
            zipWith
              (\(WithCtLoc _ (_, p)) ct -> (CType p, ct))
              locConsts
              cts
        )
  tcPluginTrace "deferrable: " $
    ppr cts
  pure cts

buildEv ::
  NameTbl -> WithCtLoc (Ct, Type) -> TcPluginM Ct
buildEv tbl@NameTbl {..} (WithCtLoc loc (ct, ty)) = do
  let defTy = mkAppTy (mkTyConTy $ classTyCon _Deferrable) ty
  g <-
    newGiven loc defTy $
      buildUndeferred tbl ty $
        ctEvExpr (ctEvidence ct)

  pure $ mkNonCanonical' loc g

mkNonCanonical' ::
  CtLoc -> CtEvidence -> Ct
mkNonCanonical' origCtl ev =
  let ct_ls = ctLocSpan origCtl
      ctl = ctEvLoc ev
      wanted = mkNonCanonical ev
   in setCtLoc wanted (setCtLocSpan ctl ct_ls)

trustMe' :: String -> Type -> Type -> Coercion
trustMe' msg =
  mkUnivCo
    (PluginProv $ "Data.Constraint.Deferrable.Solver: " ++ msg)
    Representational

deconsDeferrable ::
  NameTbl -> Type -> Maybe Type
deconsDeferrable NameTbl {..} ty
  | ClassPred cls [prd] <- classifyPredType ty
  , cls == _Deferrable =
      Just prd
  | otherwise = Nothing

newWantedOrHole :: CtLoc -> PredType -> TcPluginM CtEvidence
newWantedOrHole loc p@(classifyPredType -> EqPred {}) = do
  hole <- newCoercionHole p
  return $ CtWanted p (HoleDest hole) WDeriv loc
newWantedOrHole loc c = newWanted loc c
