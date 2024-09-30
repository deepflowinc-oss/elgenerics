{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Record.Plugin (plugin) where

import Control.Monad
import Data.Generics
import Data.Maybe
import GHC
import GHC.TcPluginM.Orphans ()
#if MIN_VERSION_ghc(9,0,1)
import GHC.Plugins
import GHC.Types.SourceText (SourceText(..))
#else
import GhcPlugins
#endif

plugin :: Plugin
plugin =
  defaultPlugin
    { parsedResultAction = recordExp
    , pluginRecompile = const $ return NoForceRecompile
    }

recordExp ::
  [CommandLineOption] ->
  ModSummary ->
  HsParsedModule ->
  Hsc HsParsedModule
recordExp opts _ pmods = do
  let cons = mkDataOcc $ head $ opts ++ ["MkRecord"]
  m <- everywhereM (mkM $ procRecCon cons) $ hpm_module pmods
  return $ pmods {hpm_module = m}

procRecCon ::
  OccName ->
  LHsExpr GhcPs ->
  Hsc (LHsExpr GhcPs)
procRecCon
  cons
  (L gLoc RecordCon {rcon_con = L _ (Unqual c), rcon_flds = HsRecFields {..}})
    | c == cons = do
        when (isJust rec_dotdot) $
          error "Wildcard in Extensible Record construction not allowed"
        toRecordCons gLoc rec_flds
procRecCon _ rc = return rc

toRecordCons :: SrcSpanAnnA -> [LHsRecField GhcPs (LHsExpr GhcPs)] -> Hsc (LHsExpr GhcPs)
toRecordCons gLoc fs = do
  recHKM <- lookupModule (mkModuleName "Data.Record.HigherKinded") Nothing
  recM <- lookupModule (mkModuleName "Data.Record") Nothing
  let emp = Orig recM $ mkVarOcc "emptyRec"
      eql = Orig recHKM $ mkDataOcc ":="
      flabl = Orig recHKM $ mkDataOcc "FieldLabel"
      flablTy = Orig recHKM $ mkTcOcc "FieldLabel"
      castE = Orig recHKM $ mkVarOcc "castRecord"
      addF = Orig recM $ mkVarOcc "&+"
      toBody (L l HsRecField {..}) =
        let L fldL fldB = hsRecFieldLbl
         in L l $
              OpApp
                EpAnnNotUsed
                ( L (noAnnSrcSpan fldL) $
                    ExprWithTySig
                      EpAnnNotUsed
                      (noLocA $ HsVar NoExtField (noLocA flabl))
                      ( HsWC NoExtField
                          $ noLocA
                          $ HsSig NoExtField (HsOuterImplicit NoExtField)
                          $ noLocA
                          $ HsAppTy
                            NoExtField
                            ( noLocA $
                                HsTyVar EpAnnNotUsed NotPromoted (noLocA flablTy)
                            )
                          $ noLocA
                          $ HsTyLit NoExtField
                          $ HsStrTy NoSourceText
                          $ occNameFS
                          $ occName
                          $ unLoc
                          $ rdrNameFieldOcc fldB
                      )
                )
                (noLocA $ HsVar NoExtField $ noLocA eql)
                hsRecFieldArg
      bdy =
        L gLoc
          $ HsApp
            EpAnnNotUsed
            (noLocA $ HsVar NoExtField $ noLocA castE)
          $ noLocA
          $ HsPar EpAnnNotUsed
          $ noLocA
          $ foldl
            ( \a b ->
                OpApp
                  EpAnnNotUsed
                  (noLocA a)
                  (noLocA $ HsVar NoExtField $ noLocA addF)
                  b
            )
            (HsVar NoExtField $ noLocA emp)
          $ map toBody fs
  return bdy
