{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Data.TypeLevel.Normalise.Plugin (plugin, Normalise) where

import Data.Generics (everywhereM, mkM)
#if MIN_VERSION_ghc(9,0,1)
#if MIN_VERSION_ghc(9,2,0)
import GHC.Unit.Finder
import GHC.Tc.Solver
#else
import GHC.Driver.Finder (findPluginModule)
#endif
import GHC.Hs.Decls
import GHC.Hs.Extension
import GHC.Hs.Type
import GHC.Plugins
import GHC.Iface.Env (lookupOrig)
import GHC.Tc.Utils.Env
import GHC.Tc.Gen.HsType
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.Zonk (zonkTcTypeToType)
import GHC.Tc.Instance.Family
import GHC.Core.FamInstEnv (normaliseType)
#else
import FamInst (tcGetFamInstEnvs)
import FamInstEnv (normaliseType)
import Finder (findPluginModule)
import GHC.Hs.Decls
import GHC.Hs.Extension
import GHC.Hs.Types
import GhcPlugins
import IfaceEnv (lookupOrig)
import TcEnv
import TcHsSyn
import TcHsType
import TcRnMonad
#endif

type family Normalise (a :: k) :: k where
  Normalise a = a

{- | @'Normalise' ty@ の形の型の @ty@ 部分の型族を可能な限り展開した形にする
   型検査器プラグイン。ワイルドカードは未対応（面倒なので）。

   * Normalise シノニムで包まれた型族の適用を可能な限り展開する
     * 他モジュールで定義されたものしか扱えない限定あり
   * 簡約が可能な制約があれば、簡約してメモ化
     * あんまり効果なさそう
   * 型検査通過後、簡約可能な型シノニムを可能な限り展開する
       更に型レベルの計算の重複を削減出来る
-}
plugin :: Plugin
plugin =
  defaultPlugin
    { pluginRecompile = purePlugin
    , renamedResultAction = reducer
    , typeCheckResultAction = \flags ->
        if "specified-only" `elem` flags
          then const pure
          else const reduceTcGbl
    }

reduceTcGbl ::
  TcGblEnv -> TcM TcGblEnv
reduceTcGbl env = do
  tcs <- mapM reduceTyCon $ tcg_tcs env
  pure env {tcg_tcs = tcs}

reduceTyCon :: TyCon -> TcM TyCon
reduceTyCon tyCon
  | Just rhs <- synTyConRhs_maybe tyCon
  , not $ tyConResKind tyCon `eqType` constraintKind =
      do
        rhs' <- reduceType rhs
        let binders = tyConBinders tyCon
        if rhs `eqType` rhs'
          then pure tyCon
          else do
            let tyCon' =
                  mkSynonymTyCon
                    (tyConName tyCon)
                    binders
                    (tyConResKind tyCon)
                    (tyConRoles tyCon)
                    rhs'
                    (isTauTyCon tyCon)
                    (isFamFreeTyCon tyCon)
                    (isForgetfulSynTyCon tyCon)
            traceRn "Normed: " $ ppr (tyCon, tyCon')
            pure tyCon'
  | otherwise = pure tyCon

reducer :: [CommandLineOption] -> TcGblEnv -> HsGroup GhcRn -> TcM (TcGblEnv, HsGroup GhcRn)
reducer _ gblEnv grp = do
  env <- getTopEnv
  Found _ ovlMod <-
    liftIO $ findPluginModule env $ mkModuleName "Data.TypeLevel.Normalise.Plugin"
  normName <- lookupOrig ovlMod (mkTcOcc "Normalise")
  setGblEnv gblEnv $
    (gblEnv,) <$> everywhereM (mkM $ rewriteNormalise normName) grp

rewriteNormalise :: Name -> TyClDecl GhcRn -> TcM (TyClDecl GhcRn)
rewriteNormalise
  norm
  sdecl@SynDecl {tcdTyVars = HsQTvs _ exps} = do
    tys <- mapM (\(L _ a) -> resolveTyVarBndr a) exps
    tcExtendTyVarEnv tys $ everywhereM (mkM $ rewriteHsTy norm) sdecl
rewriteNormalise norm dcl = everywhereM (mkM $ rewriteHsTy norm) dcl

resolveTyVarBndr :: HsTyVarBndr a GhcRn -> TcM TyVar
resolveTyVarBndr (UserTyVar _ _ (L _ n)) = do
  pure $ mkTyVar n liftedTypeKind
resolveTyVarBndr (KindedTyVar _ _ (L _ n) lk) = do
  kind <- tcLHsKindSig (GhciCtxt False) lk
  pure $ mkTyVar n kind
#if !MIN_VERSION_ghc(9,0,1)
resolveTyVarBndr (XTyVarBndr vacuous) = noExtCon vacuous
#endif

rewriteHsTy :: Name -> HsType GhcRn -> TcM (HsType GhcRn)
rewriteHsTy norm (HsAppTy _ (L _ (HsTyVar _ NotPromoted (L _ nm))) rhs)
  | nm == norm = fmap XHsType . reduceType =<< fromLHsType rhs
rewriteHsTy _ ty = pure ty

fromLHsType :: LHsType GhcRn -> TcM Type
fromLHsType ty = do
  -- Copied partially from @tcRnType@
  (ty', _) <- pushTcLevelM_ $ solveEqualities "fromLHsType" $ tcInferLHsTypeKind ty
  zonkTcTypeToType ty'

reduceType :: Type -> TcM Type
reduceType ty = do
  envs <- tcGetFamInstEnvs
  pure $ snd $ normaliseType envs Nominal ty
