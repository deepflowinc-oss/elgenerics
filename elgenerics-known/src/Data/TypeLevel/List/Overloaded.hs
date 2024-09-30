{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

module Data.TypeLevel.List.Overloaded (plugin, PElement, PIsList (..)) where

import Data.Generics (everywhere, mkT)
import GHC
#if MIN_VERSION_ghc(9,0,1)
#if MIN_VERSION_ghc(9,2,0)
import GHC.Unit.Finder
import GHC.Types.TyThing
#else
import GHC.Driver.Finder
#endif
import GHC.Tc.Utils.Monad
import GHC.Plugins
import GHC.Iface.Env (lookupOrig)
#else
import Finder
import GhcPlugins
import IfaceEnv
import TcRnMonad
#endif

type family PElement ty

class PIsList ty where
  type FromList (as :: [PElement ty]) :: ty
  type Cons (a :: PElement ty) (as :: ty) :: ty
  type Empty :: ty

type instance PElement [a] = a

instance PIsList [a] where
  type FromList xs = xs
  type Cons x xs = x ': xs
  type Empty = '[]

plugin :: Plugin
plugin =
  defaultPlugin
    { renamedResultAction = overloadTyLists
    , pluginRecompile = purePlugin
    }

data Symbols = Symbols
  { emptySymbol :: TyCon
  , consSymbol :: TyCon
  , fromListSymbol :: TyCon
  }

overloadTyLists ::
  [CommandLineOption] ->
  TcGblEnv ->
  HsGroup GhcRn ->
  TcM (TcGblEnv, HsGroup GhcRn)
overloadTyLists _ gblEnv grp = do
  env <- getTopEnv
  Found _ ovlMod <-
    liftIO $ findPluginModule env $ mkModuleName "Data.TypeLevel.List.Overloaded"
  fromListSymbol <- lookupTyCon =<< lookupOrig ovlMod (mkTcOcc "FromList")
  consSymbol <- lookupTyCon =<< lookupOrig ovlMod (mkTcOcc "Cons")
  emptySymbol <- lookupTyCon =<< lookupOrig ovlMod (mkTcOcc "Empty")
  let symbs = Symbols {..}
  pure (gblEnv, everywhere (mkT $ overloadTy symbs) grp)

defTyVarX :: XTyVar GhcRn
#if MIN_VERSION_ghc(9,2,5)
defTyVarX = EpAnnNotUsed
#else
defTyVarX = NoExtField
#endif

noLoc' :: e -> GenLocated (SrcSpanAnn' (EpAnn ann)) e
noLoc' = L (SrcSpanAnn EpAnnNotUsed generatedSrcSpan)

overloadTy :: Symbols -> HsType GhcRn -> HsType GhcRn
overloadTy Symbols {..} (HsExplicitListTy _ _ []) =
  HsTyVar defTyVarX NotPromoted $ noLoc' $ tyConName emptySymbol
overloadTy Symbols {..} tyList@(HsExplicitListTy {}) =
  HsAppTy
    NoExtField
    (noLoc' $ HsTyVar defTyVarX NotPromoted (noLoc' $ tyConName fromListSymbol))
    $ noLoc' tyList
overloadTy Symbols {..} (HsOpTy _ l (L loc nam) r)
  | nam == consDataConName =
      HsOpTy NoExtField l (L loc $ tyConName consSymbol) r
overloadTy _ ty = ty
