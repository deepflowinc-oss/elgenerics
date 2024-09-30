{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Data.TypeLevel.List.Solver.Free where

import Control.Applicative
import Control.Arrow
import Control.Lens (uses, view, (%=), (%~), (<&>), (^?), _1, _2, _Just)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Primitive
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State.Strict
import qualified Data.DList as DL
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as Set
import Data.TypeLevel.List.Solver.Reduce
import Data.TypeLevel.List.Solver.Syntax
import Data.TypeLevel.List.Solver.Utils
import GHC.Stack
import GHC.TcPluginM.Extra
import GHC.TcPluginM.Orphans ()
#if MIN_VERSION_ghc(9,0,1)
import GHC.Tc.Types.Constraint
import GHC.Core.FamInstEnv (normaliseType)
import GHC.Plugins
  ( Expr (..),
    PredType,
    TcTyVar,
    Type,
    eqType,
  )
import GHC.Tc.Plugin hiding (newWanted)
import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.TcType (TcPredType)
#else
import Constraint
import FamInstEnv (normaliseType)
import GhcPlugins
  ( Expr (..),
    PredType,
    TcTyVar,
    Type,
    eqType,
  )
import TcEvidence
import TcPluginM hiding (newWanted)
import TcRnTypes
import TcType (TcPredType)
#endif

type Goal = Ct

type Givens = Map Constr CtEvidence

type Witness = EvTerm

data Dictionary = Dictionary
  { dictExpr :: EvExpr
  , dictPred :: PredType
  , dictLoc :: CtLoc
  }

data SolverF a where
  CurrentGoal :: SolverF (Maybe Goal)
  Givens :: SolverF Givens
  Require :: Constr -> SolverF Dictionary
  SymbolTable :: SolverF SymbolTable
  ToWitness :: Dictionary -> SolverF Witness
  LiftTcPluginM :: TcPluginM a -> SolverF a

data Free f a where
  Pure :: a -> Free f a
  Fail :: Free f a
  Choice :: Free f a -> Free f a -> Free f a
  Bind :: f b -> (b -> Free f a) -> Free f a

instance Functor (Free f) where
  fmap _ Fail = Fail
  fmap f (Choice ma mb) = Choice (f <$> ma) (f <$> mb)
  fmap f (Pure a) = Pure $ f a
  fmap f (Bind fb fba) =
    Bind fb $ Pure . f <=< fba

instance Applicative (Free f) where
  pure = Pure
  (<*>) = ap

instance Monad (Free f) where
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 808
  fail = const Fail
#endif
  Pure a >>= f = f a
  Fail >>= _ = Fail
  Choice l r >>= f = Choice (f =<< l) (f =<< r)
  Bind fa g >>= f = Bind fa (g >=> f)

instance MonadFail (Free f) where
  fail = const Fail

instance Alternative (Free f) where
  empty = Fail
  Fail <|> r = r
  l <|> Fail = l
  l <|> r = Choice l r

instance MonadPlus (Free f) where
  mzero = Fail
  mplus = (<|>)

interp ::
  (Monad m, Alternative m) =>
  (forall x. f x -> m x) ->
  Free f a ->
  m a
interp trans = go
  where
    go (Pure a) = return a
    go Fail = empty
    go (Choice l r) = go l <|> go r
    go (Bind fa g) = go . g =<< trans fa

tryInterp ::
  (Monad m) =>
  (forall x. f x -> m x) ->
  Free f a ->
  m (Maybe a)
tryInterp trans = runMaybeT . interp (lift . trans)

embed :: f a -> Free f a
embed = flip Bind return

require :: Constr -> Solver Dictionary
require = Solver . embed . Require

getSymbolTable :: Solver SymbolTable
getSymbolTable = Solver $ embed SymbolTable

getCurrentGoal :: Solver (Maybe Goal)
getCurrentGoal = Solver $ embed CurrentGoal

toWitness :: Dictionary -> Solver Witness
toWitness = Solver . embed . ToWitness

getGivens :: Solver Givens
getGivens = Solver $ embed Givens

liftTcPluginM :: TcPluginM a -> Solver a
liftTcPluginM = Solver . embed . LiftTcPluginM

newtype Solver a = Solver {runSolver :: Free SolverF a}
  deriving newtype (Functor, Applicative, MonadPlus, Alternative, MonadFail, Monad)

type EvidenceDic = Map WType CtEvidence

type Normalisation = Map WType (TcCoercion, Type)

data ListSolverState = LSS
  { reduction :: IORef (Set.Set (Term, Term))
  , symTbl :: SymbolTable
  , toBeReduced :: IORef (Set.Set (WithCtLoc Constr))
  , doneRef :: IORef (Set.Set (WithCtLoc Constr))
  , eqDicRef :: IORef EvidenceDic
  , normDic :: IORef Normalisation
  }

runSolveMode ::
  HasCallStack =>
  [(TcTyVar, Type)] ->
  SymbolTable ->
  TcRef EvidenceDic ->
  IORef Normalisation ->
  [Ct] -> -- Givens
  Ct -> -- Goal
  Solver a ->
  TcPluginM (Maybe (a, [Ct]))
runSolveMode subs stbl evDicRef normRefs gs goal0 (Solver act) = do
  givens <- buildGivenDic stbl normRefs gs
  let goal = substCt subs goal0
  evDic <- tcPluginIO $ readIORef evDicRef
  let go :: SolverF a -> StateT (EvidenceDic, DL.DList Ct) (MaybeT TcPluginM) a
      go Givens = pure givens
      go SymbolTable = pure stbl
      go (Require c0) = do
        let redC0 = reduceC stbl c0
        (_, redP) <- lift $ lift $ normaliseIt normRefs $ fromConstr stbl redC0
        let redC = toConstr stbl redP
            origP = fromConstr stbl c0
            gsRed = M.lookup redC givens
        redCands <- (gsRed <|>) <$> (uses _1 (M.lookup (WType redP)))
        pf <- case redCands of
          Just ev -> return ev
          Nothing -> do
            ev <- lift $ lift $ newWantedOrHole goal stbl redC
            case redC of
              EqType {} -> _1 %= M.insert (WType redP) ev
              _ -> return ()
            _2 %= (`DL.snoc` mkNonCanonical ev)
            return ev
        return $
          if redP `eqType` origP
            then ctEvToDictionary pf
            else
              Dictionary
                { dictExpr =
                    ctEvExpr pf
                      `Cast` trustMe' "runSolveMode" redP origP
                , dictPred = origP
                , dictLoc = ctev_loc pf
                }
      go CurrentGoal = pure $ Just goal0
      go ToWitness {} = empty
      go (LiftTcPluginM a) = lift $ lift a
  mans <-
    runMaybeT $
      runStateT (interp go act) (evDic, DL.empty)
        <&> _2 . _2 %~ DL.toList
  forM_ (mans ^? _Just . _2 . _1) $
    tcPluginIO . writeIORef evDicRef
  return ((view _1 &&& view (_2 . _2)) <$> mans)

newWantedOrHole :: Ct -> SymbolTable -> Constr -> TcPluginM CtEvidence
newWantedOrHole ct stbl eql@(EqType _ _ _) = do
  let p = fromConstr stbl eql
  hole <- newCoercionHole p
  return $ CtWanted p (HoleDest hole) WDeriv (ctLoc ct)
newWantedOrHole ct stbl c = do
  let p = fromConstr stbl c
  newWanted (ctLoc ct) p

runGenerationMode ::
  SymbolTable ->
  IORef Normalisation ->
  Givens ->
  Solver a ->
  TcPluginM (Maybe a)
runGenerationMode stbl normRefs givens (Solver act) = do
  let go :: SolverF a -> MaybeT TcPluginM a
      go Givens = pure givens
      go SymbolTable = pure stbl
      go (Require c) = do
        c' <-
          lift $
            fmap (toConstr stbl . snd) $
              normaliseIt normRefs $
                fromConstr stbl c
        Just l <- return $ M.lookup c' givens
        return $
          Dictionary
            { dictExpr = ctEvExpr l
            , dictPred = ctEvPred l
            , dictLoc = ctev_loc l
            }
      go CurrentGoal = empty
      go ToWitness {} = empty
      go (LiftTcPluginM a) = lift a
  runMaybeT $ interp go act

buildGivenDic ::
  SymbolTable ->
  IORef Normalisation ->
  [Ct] ->
  TcPluginM Givens
buildGivenDic stbl norms givens =
  let subst = mkSubst' givens
      subst' = map fst subst
   in M.fromList
        <$> mapM
          ( \ct -> do
              let new = substCt subst' ct
                  p0 = ctPred new
              (_, p') <- normaliseIt norms p0
              pure
                ( toConstr stbl p'
                , (ctEvidence new) {ctev_pred = ctPred ct}
                )
          )
          givens

normaliseIt :: IORef Normalisation -> PredType -> TcPluginM (TcCoercion, TcPredType)
normaliseIt normRef ty = do
  instEnvs <- getFamInstEnvs
  tcPluginIO $
    atomicModifyIORef' normRef $ \norms ->
      case M.lookup (WType ty) norms of
        Just normed -> (norms, normed)
        Nothing ->
          let normed' = normaliseType instEnvs Nominal ty
           in (M.insert (WType ty) normed' norms, normed')

unsafeDicToWitnessM ::
  HasCallStack => Dictionary -> Solver Witness
unsafeDicToWitnessM dic = do
  Just ct <- getCurrentGoal
  let orig = ctPred ct
      targ = dictPred dic
  return $ dictExpr dic `evCast` trustMe' ("unsafeDicToWitnessM: " ++ show callStack) targ orig

unsafeDicToWitnessFor :: Either PredType Constr -> Dictionary -> Solver Witness
unsafeDicToWitnessFor ecnstr dic = do
  stbl <- getSymbolTable
  let orig = either id (fromConstr stbl) ecnstr
      targ = dictPred dic
  return $ dictExpr dic `evCast` trustMe' "unsafeDicToWitnessFor" targ orig

instance MonadIO Solver where
  liftIO = liftTcPluginM . tcPluginIO
  {-# INLINE liftIO #-}

instance PrimMonad Solver where
  type PrimState Solver = RealWorld
  primitive = liftTcPluginM . primitive
  {-# INLINE primitive #-}

ctEvToDictionary :: CtEvidence -> Dictionary
ctEvToDictionary ev =
  Dictionary
    { dictPred = ctEvPred ev
    , dictExpr = ctEvExpr ev
    , dictLoc = ctev_loc ev
    }
