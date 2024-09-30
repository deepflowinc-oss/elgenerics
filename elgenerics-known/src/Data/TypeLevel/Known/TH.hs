{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE ViewPatterns #-}
module Data.TypeLevel.Known.TH
  ( deriveAllKnown,
    defineSingletons,
    deriveKnown,
    deriveSTestEquality,
    deriveSingTypeable,
    sCases,
  deriveShowSing)
where

import qualified Control.Foldl as L
import Control.Lens (anyOf, cosmos, to, transform, (%~), (&), (^..), _head)
import Control.Monad
import Data.Char (toLower)
import Data.Foldable (Foldable (foldl'), toList)
import qualified Data.Kind as K
import qualified Data.Set as Set
import Data.Type.Equality
import Data.TypeLevel.Known.Core
import GHC.Generics (Generic)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Lens (_VarT)
import Type.Reflection (Typeable, typeRep)
import Unsafe.Coerce
import qualified Data.Kind as Kinds
import Data.Maybe (catMaybes)
import TH.Utilities (typeToNamedCon)

data DataSeed = DataSeed
  { isNew :: NewOrData
  , dataContext :: DCxt
  , typeName :: Name
  , tyvarBndrs :: [DTyVarBndr ()]
  , constructors :: [DCon]
  , singDataName :: Name
  , dfullyInstTy :: DType
  , knownClassName :: Name
  , singInfos :: [SingInfo]
  , argTySet :: Set.Set Type
  , argTys :: [Type]
  , testEqCtx :: [Type]
  }

withDataSeed ::
  (DataSeed -> Q a) -> Name -> Q a
withDataSeed f n = do
  Just (DTyConI (DDataD isNew dataContext typeName tyvarBndrs _ constructors _) _) <- dsReify n
  unless (null dataContext) $ fail "DatatypeContexts not yet supported"
  let singDataName = mkName $ 'S' : nameBase typeName
      dtys = map dTyVarBndrToDType tyvarBndrs
      dfullyInstTy = foldl DAppT (DConT typeName) dtys
      knownClassName = mkName $ "Known" ++ nameBase typeName
  singInfos <- mapM (buildSingInfos singDataName) constructors
  let argTySet =
        L.fold
          ( L.premap singFields $
              L.handles L.folded $
                L.premap (sweeten . snd) $
                  L.set
          )
          singInfos
      argTys = Set.toList argTySet
      testEqCtx = [ConT ''STestEquality `AppT` ty | ty <- argTys]

  f DataSeed {..}

deriveShowSing :: Name -> DecsQ
deriveShowSing = fmap pure . withDataSeed deriveShowSingWith

deriveSTestEquality :: Name -> DecsQ
deriveSTestEquality = fmap pure . withDataSeed deriveSTestEqualityWith

defineSingletons :: Name -> DecsQ
defineSingletons = withDataSeed defineSingletonsWith

deriveKnown :: Name -> Q [Dec]
deriveKnown = withDataSeed deriveKnownWith

defineSingletonsWith :: DataSeed -> DecsQ
defineSingletonsWith DataSeed {..} = do
  x <- newName "_x"
  let singDataDecl = DataD
          []
          singDataName
          [KindedTV x () $ sweeten dfullyInstTy]
          Nothing
          [ GadtC [singConName]
              (map
                ((Bang NoSourceUnpackedness NoSourceStrictness ,) . sweeten)
                singConArgTypes
              )
              (sweeten singConRetType)
          | SingInfo {..} <- singInfos
          ]
          []
      singKindSig = DKiSigD singDataName
        $ DArrowT `DAppT` dfullyInstTy `DAppT` DConT ''Kinds.Type
  pure $
    decsToTH
      [
#if __GLASGOW_HASKELL__ >= 810
        singKindSig
#endif
      ]
    ++ [ singDataDecl ]

deriveAllKnown ::
  -- | KnownHoge 系の制約シノニムを定義するか?
  Bool ->
  Name ->
  DecsQ
deriveAllKnown defKnown = withDataSeed $
  \ds@DataSeed {..} -> do
    a <- newName "_a"
    let bndr = map (asSpecified . sweeten) tyvarBndrs
        dtys = map dTyVarBndrToDType tyvarBndrs
        tys = map sweeten dtys
        fullTy = sweeten dfullyInstTy
        knownArg = varT a `sigT` fullTy
        someTyName = mkName $ "Some" ++ nameBase typeName
        someTy = foldl' AppT (ConT someTyName) tys
    knownSynCls <-
      classD
        (pure <$> [t|Known $knownArg|])
        knownClassName
        [KindedTV a () fullTy]
        []
        []
    knownSynInst <-
      instanceD
        (pure <$> [t|Known $knownArg|])
        [t|$(conT knownClassName) $(varT a)|]
        []
    let demFullTyQ =
          foldl
            appT
            (conT typeName)
            [ if unSigT ty `Set.member` argTySet
              then [t|Demote $(pure ty)|]
              else pure ty
            | ty <- tys
            ]
    x <- newName "_x"
    singDec <- defineSingletonsWith ds
    stestInstD <- deriveSTestEqualityWith ds
    sShowInstD <- deriveShowSingWith ds

    testEqD <-
      instanceD
        (pure testEqCtx)
        [t|TestEquality ($(conT singDataName) :: $(pure fullTy) -> K.Type)|]
        [ funD
            'testEquality
            [ clause
                []
                ( normalB
                    [|\a_ b_ -> testEquality (WrapSing a_) (WrapSing b_)|]
                )
                []
            ]
        , pragInlD 'testEquality Inline FunLike AllPhases
        ]

    promoteBody <-
      lamE [varP x] $
        caseE
          (varE x)
          $ map buildPromote singInfos

    demoteBody <-
      lamE [varP x] $
        caseE
          (varE x)
          $ map buildDemote singInfos
    let someFunCxt =
          map (ConT ''HasSing `AppT`) argTys
    someFunTy <-
      desugar
        =<< forallT bndr (pure someFunCxt) [t|$(demFullTyQ) -> $(pure someTy)|]
    let toSomeFunName = mkName $ "toSome" ++ nameBase typeName
        toSome =
          sweeten
            (map
              DLetDec
              [ DSigD toSomeFunName someFunTy
              , DFunD toSomeFunName $
                  [DClause [] (DVarE 'promote)]
              ])
          ++ [PragmaD $ InlineP 'sTestEquality Inline FunLike AllPhases]
    pxy <- newName "_pxy"
    valTy <-
      desugar
        =<< forallT
          (bndr ++ [KindedTV x SpecifiedSpec fullTy, PlainTV pxy SpecifiedSpec])
          ( pure $
              (ConT knownClassName `AppT` VarT x) :
              map (ConT ''HasSing `AppT`) argTys
          )
          [t|$(varT pxy) $(varT x) -> $(demFullTyQ)|]
    sValTy <-
      desugar
        =<< [t|
          forall x pxy.
          $(conT knownClassName) x =>
          pxy x ->
          $(conT singDataName) x
          |]
    let lowTyName = nameBase typeName & _head %~ toLower
        valName = mkName $ lowTyName ++ "Val"
        sValName = mkName $ 's' : nameBase typeName ++ "Val"
        valDefs =
          (PragmaD $ InlineP valName Inline FunLike AllPhases) :
          sweeten
            (map
              DLetDec
              [ DSigD valName valTy
              , DFunD valName [DClause [] (DVarE 'knownVal)]
              , DSigD sValName sValTy
              , DFunD sValName [DClause [] (DVarE 'sKnownVal)]
              ])
            ++ [PragmaD $ InlineP sValName Inline FunLike AllPhases]
    knowns <- deriveKnownWith ds
    singTypeableInsts <- singTypeableDecls ds
    hasSing <-
      instanceD
        (pure [ConT ''HasSing `AppT` ty | ty <- argTys])
        [t|HasSing $(pure fullTy)|]
        [ tySynInstD $
            tySynEqn
              Nothing
              [t|Demote $(pure fullTy)|]
              demFullTyQ
        , funD 'demote [clause [] (normalB $ pure demoteBody) []]
        , pragInlD 'demote Inline FunLike AllPhases
        , funD 'promote [clause [] (normalB $ pure promoteBody) []]
        , pragInlD 'promote Inline FunLike AllPhases
        ]
    someSingSyn <-
      tySynD
        someTyName
        (map sweeten tyvarBndrs)
        [t|SomeSing $(pure fullTy)|]
    tyConSyns <- forM singInfos $ \SingInfo {..} ->
      tySynD (mkName $ nameBase origConName) [] $ promotedT origConName
    return $
      singDec
        ++ [stestInstD, testEqD, sShowInstD]
        ++ knowns
        ++ tyConSyns
        ++ [hasSing]
        ++ toSome
        ++ [someSingSyn]
        ++ valDefs
        ++ singTypeableInsts
        ++ mconcat [[knownSynCls, knownSynInst] | defKnown]

asSpecified :: TyVarBndr () -> TyVarBndr Specificity
asSpecified (PlainTV na _) = PlainTV na SpecifiedSpec
asSpecified (KindedTV na _ ty) = KindedTV na SpecifiedSpec ty

deriveSTestEqualityWith :: DataSeed -> Q Dec
deriveSTestEqualityWith DataSeed {..} = do
  let noEql = [|unsafeCoerce (NonEqual :: Equality Int Bool)|]
  l <- newName "_l"
  r <- newName "_r"
  stestBody <-
    lamE [varP l, varP r] $
      caseE (tupE [varE l, varE r]) $
        map buildEqualityCase singInfos ++ [match wildP (normalB noEql) []]
  instanceWithOverlapD
    Nothing
    (pure testEqCtx)
    (conT ''STestEquality `appT` (pure $ sweeten dfullyInstTy))
    [ funD 'sTestEquality [clause [] (normalB $ pure stestBody) []]
    , pragInlD 'sTestEquality Inline FunLike AllPhases
    ]


deriveShowSingWith :: DataSeed -> DecQ
deriveShowSingWith DataSeed{..} = do
  s <- newName "s"
  standaloneDerivD (pure [ConT ''ShowSing `AppT` arg | arg <- argTys])
    [t|Show ($(conT singDataName) $(varT s `sigT` sweeten dfullyInstTy))|]


deriveKnownWith :: DataSeed -> Q [Dec]
deriveKnownWith DataSeed {..} = do
  let singInst =
        decToTH $
          DTySynInstD $
            DTySynEqn
              Nothing
              (DConT ''Sing)
              (DConT singDataName)
  knowns <- mapM buildKnown singInfos
  pure $ singInst : knowns

buildDemote :: SingInfo -> MatchQ
buildDemote SingInfo {..} = do
  let body =
        normalB $
          foldl'
            appE
            (conE origConName)
            [[|demote $(varE v)|] | (v, _) <- singFields]
  match
    (conP singConName $ map (varP . fst) singFields)
    body
    []

buildPromote :: SingInfo -> Q Match
buildPromote SingInfo {..} = do
  pVars <- mapM (newName . ("_prom_" ++) . nameBase . fst) singFields
  let resl =
        ConE 'MkSomeSing
          `AppE` foldl'
            AppE
            (ConE singConName)
            (map VarE pVars)
      gBinds =
        PatG $
          zipWith
            ( \(orig, _) d ->
                BindS (ConP 'MkSomeSing [] [VarP d]) $
                  VarE 'promote `AppE` VarE orig
            )
            singFields
            pVars
      body
        | null singFields = normalB $ pure resl
        | otherwise = guardedB [pure (gBinds, resl)]
  match
    (conP origConName $ map (varP . fst) singFields)
    body
    []

buildEqualityCase :: SingInfo -> MatchQ
buildEqualityCase SingInfo {..} = do
  lArgs <- mapM (newName . (++ "_l") . nameBase . fst) singFields
  rArgs <- mapM (newName . (++ "_r") . nameBase . fst) singFields
  let equal = ConE 'Equal
      subs =
        PatG $
          zipWith
            ( \l r ->
                BindS (ConP 'Equal [] []) $
                  foldl' AppE (VarE 'sTestEquality) [VarE l, VarE r]
            )
            lArgs
            rArgs
      body
        | null singFields = normalB $ pure equal
        | otherwise = guardedB [pure (subs, equal)]
  match
    ( tupP
        [ conP singConName $ map varP lArgs
        , conP singConName $ map varP rArgs
        ]
    )
    body
    []

buildKnown :: SingInfo -> Q Dec
buildKnown SingInfo {..} =
  instanceD
    ( sequence
        [ [t|Known $(varT var `sigT` sweeten ty)|]
        | (var, ty) <- singFields
        ]
    )
    [t|Known $(pure $ sweeten saturatedCon)|]
    [ funD
        'sKnownVal'
        [ clause
            []
            ( normalB $
                appsE $
                  conE singConName :
                  map (const [|sKnownVal'|]) singFields
            )
            []
        ]
    , pragInlD 'sKnownVal' Inline FunLike AllPhases
    ]

data SingInfo = SingInfo
  { origConName :: Name
  , singConName :: Name
  , singFields :: [(Name, DType)]
  , singRetType :: DType
  , singConArgTypes :: [DType]
  , singConRetType :: DType
  , saturatedCon :: DType
  }
  deriving (Show, Generic, Typeable)

buildSingInfos ::
  Name -> DCon -> Q SingInfo
buildSingInfos singDataName (DCon _ _ origConName flds singRetType) = do
  singFields <- parseFields flds
  let singConName = mkName $ 'S' : nameBase origConName
      singConArgTypes = map (\(v, ty) -> DConT ''Sing `DAppT` (DVarT v `DSigT` ty)) singFields
      saturatedCon =
        foldl' DAppT (DConT origConName) $
          map (DVarT . fst) singFields
      singConRetType = (DConT singDataName `DAppT` saturatedCon)
  pure SingInfo {..}

parseFields :: DConFields -> Q [(Name, DType)]
parseFields (DNormalC _ fs) =
  mapM (\(_, ty) -> (,ty) <$> newName "_v") fs
parseFields (DRecC fs) =
  pure $ map (\(var, _, ty) -> (var, ty)) fs

unSigT :: Type -> Type
unSigT (SigT l _) = unSigT l
unSigT t = t

sCases ::
  -- | A type to match on its singleton ('Bool', not 'SBool'!)
  Name ->
  -- | A singleton expression to match on (scrutinee)
  ExpQ ->
  -- | Case body
  ExpQ ->
  ExpQ
sCases tyName scrutinee body = do
  Just (DTyConI _ (Just fs)) <- dsReify ''Sing
  let tyCons =
        [ con | DTySynInstD (DTySynEqn _ _ ty) <- fs
        , Just (con, _) <- pure $ typeToNamedCon $ unSigT $ sweeten ty
        ]
  conKinds <- catMaybes <$> mapM (\con -> fmap (con,) <$> dsReifyType con) tyCons
  let singTy = head
        [con
        | (con, unForAllT -> DAppT (DAppT DArrowT ty) _) <- conKinds
        , (name', _) <- toList $ typeToNamedCon (sweeten ty)
        , name' == tyName
        ]
  Just (DTyConI (DDataD _ _ _ _ _ dcons _) _) <- dsReify singTy
  caseE
    scrutinee
    [ match (recP conName []) (normalB body) []
    | DCon _ _ conName _ _ <- dcons
    ]

unForAllT :: DType -> DType
unForAllT (DForallT _ d) = unForAllT d
unForAllT (DConstrainedT _ d) = unForAllT d
unForAllT ty = ty

deriveSingTypeable ::
  Name -> DecsQ
deriveSingTypeable = withDataSeed singTypeableDecls

singTypeableDecls :: DataSeed -> Q [Dec]
singTypeableDecls DataSeed {..} = do
  let fullTy = sweeten dfullyInstTy
      targTy =
        transform
          ( \case
              (SigT l _) -> l
              t -> t
          )
          fullTy
      typeableVars =
        Set.toList $
          Set.fromList (fullTy ^.. cosmos . _VarT . to VarT)
            Set.\\ argTySet
  concretes <-
    filterM
      ( \ty -> do
          ty' <- dsType ty
          let isSelf = sweeten ty' == targTy
          pure $ anyOf cosmos (\case VarT {} -> True; _ -> False) ty && not isSelf
      )
      argTys
  ins <-
    instanceD
      ( (<>) <$> mapM (\arg -> [t|SingTypeable $(pure arg)|]) concretes
          <*> mapM (\ty -> [t|Typeable $(pure ty)|]) typeableVars
      )
      [t|SingTypeable $(pure fullTy)|]
      [ funD
          'singTypeRep
          [ do
            vs <- mapM (const $ newName "_v") singFields
            clause
              [conP singConName $ map varP vs]
              ( normalB $
                  foldr
                    (\v bdy -> [|withSingTypeable $(varE v) $bdy|])
                    [|typeRep|]
                    vs
              )
              []
          | SingInfo {..} <- singInfos
          ]
      , pragInlD 'singTypeRep Inline FunLike AllPhases
      ]
  pure [ins]
