{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module GHC.TcPluginM.Orphans () where

import Control.Monad.IO.Class
import Control.Monad.Primitive
#if MIN_VERSION_ghc(9,0,1)
import GHC
import GHC.Plugins
import GHC.Tc.Plugin
import Control.Exception.Safe
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import GHC.Utils.Error

#else
import GHC
import Exception
import GhcPlugins
import TcPluginM
#endif

instance MonadIO TcPluginM where
  liftIO = tcPluginIO

instance PrimMonad TcPluginM where
  type PrimState TcPluginM = PrimState IO
  primitive = tcPluginIO . primitive

#if MIN_VERSION_ghc(9,0,1)
deriving via ReaderT HscEnv (StateT WarningMessages IO) 
  instance MonadThrow Hsc
deriving via ReaderT HscEnv (StateT WarningMessages IO) 
  instance MonadCatch Hsc
deriving via ReaderT HscEnv (StateT WarningMessages IO) 
  instance MonadMask Hsc

#else
instance ExceptionMonad Hsc where
  gcatch (Hsc f) cth = Hsc $ \a b ->
    f a b `catch` \e ->
      case cth e of
        Hsc k -> k a b
  gmask withRestore = Hsc $ \a b ->
    gmask $ \restoreIO ->
      case withRestore (\(Hsc g) -> Hsc $ \x y -> restoreIO $ g x y) of
        Hsc k -> k a b
#endif

instance GhcMonad Hsc where
  getSession = Hsc $ \e w -> return (e, w)
  setSession = const $ error "Cannot set session in Hsc"
