{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Data.TypeLevel.List.Solver.Reduce where

import Control.Lens.Plated
import Control.Monad
import Control.Monad.Trans.RWS.Strict
import Data.Set (Set)
import Data.Set qualified as Set
import Data.TypeLevel.List.Solver.Syntax

type Equality' syntax = (Term' syntax, Term' syntax)

type Equality = Equality' Ghc

type Machine syntax =
  RWS (Set (Term' syntax, Term' syntax)) () (Set (Equality' syntax))

rewritesTo ::
  (Syntax syntax) =>
  Term' syntax ->
  Term' syntax ->
  Machine syntax (Maybe (Term' syntax))
rewritesTo l r = do
  there <- asks (\f -> (l, r) `Set.member` f || (r, l) `Set.member` f)
  unless (there || l == r) $
    modify $
      Set.insert (l, r)
  return $ Just r

deriveEquality ::
  Set (Term, Term) -> SymbolTable -> Constr -> Set Equality
deriveEquality red stbl (UnknownC ty) = deriveEqTerm red (toTerm stbl ty)
deriveEquality red _ c = foldMap (deriveEqTerm red) c

deriveEqTerm :: Set (Term, Term) -> Term -> Set Equality
deriveEqTerm red x = fst $ execRWS (rewriteM reduceM x) red (Set.empty)

reduce :: (Syntax syntax) => Term' syntax -> Term' syntax
reduce x =
  fst $
    evalRWS
      (rewriteM reduceM x)
      Set.empty
      Set.empty

reduceC ::
  SymbolTable -> Constr -> Constr
reduceC stbl (UnknownC ty) =
  UnknownC $ fromTerm stbl $ reduce (toTerm stbl ty)
reduceC _ c = fmap reduce c

reduceM :: (Syntax syntax) => Term' syntax -> Machine syntax (Maybe (Term' syntax))
reduceM t@(SortByAux' k cmp _ xs) = do
  reduceM xs >>= \case
    Just xs' ->
      rewritesTo t $
        SortByAux' k cmp (Length' k xs') xs'
    Nothing -> return Nothing
reduceM t@(Length' _ (Map' _ a _ _ xs)) = do
  rewritesTo t (Length' a xs)
reduceM t@(ElemAt' _ n (Map' b a _ h xs)) = do
  let inner = ElemAt' a n xs
  rewritesTo t $ Apply' b h inner
reduceM t@(Map' b k k' h (Take' _ n xs)) = do
  rewritesTo t $ Take' k' n $ Map' b k k' h xs
reduceM t@(Map' b k k' h (Drop' _ n xs)) = do
  rewritesTo t $ Drop' k' n $ Map' b k k' h xs
reduceM t@(ElemAt' _ (Index' _ x xs) ys) | xs == ys = do
  rewritesTo t x
reduceM t@(AppList' k (AppList' _ xs ys) zs) =
  rewritesTo t (AppList' k xs (AppList' k ys zs))
reduceM t@(Map' b k k' h (AppList' _ xs ys)) = do
  let (l, r) = (Map' b k k' h xs, Map' b k k' h ys)
  rewritesTo t $ AppList' k' l r
reduceM _ = return Nothing

-- TODO: Monotonicity
