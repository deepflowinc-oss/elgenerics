{-# LANGUAGE CPP #-}

module Data.TypeLevel.List.Solver.Utils where

import Control.Applicative
import Control.Arrow
import Control.Lens (elemOf)
import Control.Lens.Plated
import Data.Function
import Data.Ord
#if MIN_VERSION_ghc(9,0,1)
import GHC.Core.Class
import GHC.Core.Predicate
import GHC.Tc.Plugin
import GHC.Plugins hiding ((<>))
import GHC.Core.TyCo.Rep
import GHC.Tc.Types.Constraint
#else
import Class
import Constraint
import GhcPlugins hiding ((<>))
import Predicate
import TcPluginM hiding (newWanted)
import TyCoRep (UnivCoProvenance (..))
#endif

trustMe :: Type -> Type -> Coercion
trustMe = mkUnivCo (PluginProv "Data.TypeLevel.List.Solver") Representational

trustMe' :: String -> Type -> Type -> Coercion
trustMe' msg =
  mkUnivCo
    (PluginProv $ "Data.TypeLevel.List.Solver: " ++ msg)
    Representational

trustMeNominal :: Type -> Type -> Coercion
trustMeNominal = mkUnivCo (PluginProv "Data.TypeLevel.List.Solver") Nominal

myTrace :: (Outputable a) => String -> a -> TcPluginM ()
myTrace lab a =
  tcPluginIO $ putStrLn $ lab <> ": " <> showSDocUnsafe (ppr a)

typeKindElem :: Type -> Kind
typeKindElem = head . snd . splitTyConApp . typeKind

deconsPred :: PredType -> Maybe (TyCon, [Type])
deconsPred pd =
  first classTyCon <$> getClassPredTys_maybe pd
    <|> splitTyConApp_maybe pd

showOut :: (Outputable a) => a -> String
showOut = showSDocUnsafe . ppr

newtype SubtermOrd a = SubtermOrd {runSubtermOrd :: a}
  deriving (Eq)

instance (Eq a, Plated a) => Ord (SubtermOrd a) where
  SubtermOrd x <= SubtermOrd y = elemOf cosmos x y

(<@) :: (Eq a, Plated a) => a -> a -> Bool

infix 4 <@

(<@) = (<) `on` SubtermOrd

compareSubterm :: (Eq a, Plated a) => a -> a -> Ordering
compareSubterm = comparing SubtermOrd

mkNonCanonical' ::
  CtLoc -> CtEvidence -> Ct
mkNonCanonical' origCtl ev =
  let ct_ls = ctLocSpan origCtl
      ctl = ctEvLoc ev
      wanted = mkNonCanonical ev
   in setCtLoc wanted (setCtLocSpan ctl ct_ls)

showSDocExplicit :: SDoc -> String
showSDocExplicit = showSDocUnsafe
