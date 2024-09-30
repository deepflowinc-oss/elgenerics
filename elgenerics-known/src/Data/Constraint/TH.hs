{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Data.Constraint.TH (
  deriveTupleDeferrable,
  deriveDeferrableTransitively,
) where

import Control.Monad
import Data.Constraint.Deferrable
import Data.Foldable
import Data.Functor ((<&>))
import Data.Proxy
import Language.Haskell.TH
import Language.Haskell.TH.Datatype (applySubstitution, resolveTypeSynonyms, unifyTypes)
import TH.Utilities (tyVarBndrName, typeToNamedCon)

-- | Derives
deriveTupleDeferrable :: Int -> DecsQ
deriveTupleDeferrable n = do
  vs@(v0 : vs_) <- replicateM n (newName "a")
  insts <- isInstance ''Deferrable [foldl' AppT (TupleT n) $ map VarT vs]
  if insts
    then pure []
    else
      pure <$> do
        r <- newName "r"
        instanceD
          (sequence [[t|Deferrable $(varT x)|] | x <- vs])
          [t|Deferrable $(foldl' appT (tupleT n) $ map varT vs)|]
          [ funD
              'deferEither
              [ clause
                  [wildP, varP r]
                  ( normalB $
                      foldr
                        (\v k -> [|join $ deferEither (Proxy :: Proxy $(varT v)) $k|])
                        [|deferEither (Proxy :: Proxy $(varT v0)) $(varE r)|]
                        vs_
                  )
                  []
              ]
          ]

splitCtx :: Type -> ([Name], Cxt, Type)
splitCtx (ForallT ns c ty) =
  (map tyVarBndrName ns, c, ty)
splitCtx t = ([], [], t)

deriveDeferrableTransitively ::
  TypeQ -> DecsQ
deriveDeferrableTransitively typ = do
  r <- newName "r"
  rTy <- newName "r"
  (_, ctx0, constr) <- splitCtx <$> typ
  Just (n, args) <- typeToNamedCon <$> resolveTypeSynonyms constr
  insts <-
    reifyInstances n args <&> \is ->
      [i | i@InstanceD {} <- is]
  fmap concat $
    forM insts $ \ ~(InstanceD ovl ctx_ inst _) -> do
      subs <- unifyTypes [inst, constr]
      let inst' = applySubstitution subs inst
          ctx = map (applySubstitution subs) ctx_
          deferInner t = [|deferEither_ @($(pure t)) @(Either String $(varT rTy))|]
          bdy
            | null ctx = [|Right $(varE r)|]
            | otherwise =
                foldl'
                  (\a b -> [|join $ $b $a|])
                  ([|deferEither_ @($(pure $ head ctx)) @($(varT rTy)) $(varE r)|])
                  $ map deferInner
                  $ tail ctx
          ctxs = ctx0 ++ map (ConT ''Deferrable `AppT`) ctx

      sequence
        [ instanceWithOverlapD
            ovl
            (pure ctxs)
            [t|Deferrable $(pure inst')|]
            [ funD
                'deferEither
                [ clause [wildP, sigP (varP r) [t|($(pure inst')) => $(varT rTy)|]] (normalB bdy) []
                ]
            ]
        ]
