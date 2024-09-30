{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Data.TypeLevel.List.Solver where

#if MIN_VERSION_ghc(9,0,1)
import GHC.Plugins hiding (TcPlugin, (<>))
#elif MIN_VERSION_ghc(8,8,1)
import GhcPlugins hiding (TcPlugin, (<>))
#else
import GhcPlugins hiding ((<>))
#endif

#if MIN_VERSION_ghc(9,0,1)
import GHC.Tc.Types.Constraint
import GHC.Tc.Plugin hiding (newGiven, newWanted)
import GHC.Tc.Types
#else
import Constraint
import TcPluginM hiding (newGiven, newWanted)
import TcRnTypes
#endif

import Control.Arrow ((&&&))
import Data.IORef
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set qualified as Set
import Data.TypeLevel.List ()
import Data.TypeLevel.List.Solver.Constraint
import Data.TypeLevel.List.Solver.Free
import Data.TypeLevel.List.Solver.Generation
import Data.TypeLevel.List.Solver.Syntax
import GHC.TcPluginM.Extra

plugin :: Plugin
plugin =
  defaultPlugin
    { tcPlugin = const $ Just checker
    , pluginRecompile = const $ return NoForceRecompile
    }

checker :: TcPlugin
checker =
  TcPlugin
    { tcPluginInit = do
        LSS
          <$> tcPluginIO (newIORef Set.empty)
          <*> setupSymbolTable
          <*> tcPluginIO (newIORef Set.empty)
          <*> tcPluginIO (newIORef Set.empty)
          <*> tcPluginIO (newIORef Map.empty)
          <*> tcPluginIO (newIORef Map.empty)
    , tcPluginSolve = solve
    , tcPluginStop = \(LSS ref _ ref2 ref3 ref4 ref5) -> do
        tcPluginIO $ do
          writeIORef ref Set.empty
          writeIORef ref2 Set.empty
          writeIORef ref3 Set.empty
          writeIORef ref4 Map.empty
          writeIORef ref5 Map.empty
    }

solve ::
  ListSolverState ->
  [Ct] ->
  [Ct] ->
  [Ct] ->
  TcPluginM TcPluginResult
-- 簡約ステップ:Given として与えられた制約と、
--  IORef 越しに渡された制約の部分式から、わかる限りの
--  非自明な等式を生成する。
--
solve lss givens [] [] =
  TcPluginOk []
    <$> generateNontrivials
      lss
      givens
-- 制約解消ステップ。運が良ければ呼ばれないが、簡約ステップで所与
-- の制約だけで駄目な場合、改めて必要な制約を Wanted したりする。
solve (LSS _ stbl@STbl {} ref doneRef eqDicRef normSt) givens _dervds wanteds = do
  tcPluginTrace "LIST: Started with givens" $ ppr givens
  tcPluginTrace "LIST: Started with wanteds" $
    ppr
      (wanteds, map ((id &&& typeKind) . fst . splitAppTys . ctPred) wanteds)
  tcPluginTrace "LIST: Started with deriveds" $ ppr _dervds
  let subs = map fst $ mkSubst' givens
      ps =
        map
          (WithCtLoc <$> ctLoc <*> toConstr stbl . ctPred . substCt subs)
          wanteds
  dones <- tcPluginIO $ readIORef doneRef
  tcPluginIO $ writeIORef ref $ Set.fromList ps Set.\\ dones
  (es, needss) <-
    unzip . catMaybes
      <$> mapM (solveConstr subs stbl eqDicRef normSt givens) wanteds
  return $ TcPluginOk es $ concat needss
