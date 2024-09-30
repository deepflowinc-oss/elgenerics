{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Data.TypeLevel.Nat (
  (%+),
  (%-),
  (%<=?),
  withKnownNat,
  withKnownNatLeq,
  ShowNat,
  ShowDigit,
  deferNatLeq,
  deferNatLeqWith,
  caseNatLeq,
  tnat,
  module TN,
) where

import Control.Arrow ((&&&))
import Control.Monad
import Data.Map qualified as M
import Data.Maybe (fromMaybe)
import Data.Proxy
import Data.Type.Equality
import Data.TypeLevel.Known
import Data.TypeLevel.Ord.Internal
import GHC.Exts (proxy#)
import GHC.TypeLits
import GHC.TypeLits qualified as TL
import GHC.TypeNats as TN
import Language.Haskell.TH (ExpQ, PatQ, integerL, litP, mkName, numTyLit, varT, viewP)
import Language.Haskell.TH.Lib (TypeQ, caseE, litT, match, normalB, wildP)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Text.Read (readMaybe)
import Unsafe.Coerce

newtype WrapN a b = WrapN ((KnownNat a) => Proxy a -> b)

withKnownNat ::
  forall a.
  Word ->
  (forall n. (KnownNat (n :: Nat)) => Proxy n -> a) ->
  a
{-# INLINE withKnownNat #-}
withKnownNat i act = unsafeCoerce (WrapN act) (fromIntegral i :: Natural) Proxy

withKnownNatLeq ::
  forall ub a.
  (KnownNat ub) =>
  Proxy ub ->
  Word ->
  (forall n. (KnownNat (n :: Nat), n <= ub) => Proxy n -> a) ->
  Maybe a
{-# INLINE withKnownNatLeq #-}
withKnownNatLeq _ i act = do
  let i' = fromIntegral i :: Natural
  guard $ i' <= TN.natVal (Proxy @ub)
  pure $
    withKnownNat i $ \p@(Proxy :: Proxy k) ->
      gcastWith (unsafeCoerce (Refl @()) :: (k <=? ub) :~: 'True) $
        act p

type family ShowDigit (n :: Nat) :: Symbol where
  ShowDigit 0 = "0"
  ShowDigit 1 = "1"
  ShowDigit 2 = "2"
  ShowDigit 3 = "3"
  ShowDigit 4 = "4"
  ShowDigit 5 = "5"
  ShowDigit 6 = "6"
  ShowDigit 7 = "7"
  ShowDigit 8 = "8"
  ShowDigit 9 = "9"

type ShowNat n = ShowNatAux 'False "" n

type family ShowNatAux (showZero :: Bool) (heads :: Symbol) (n :: Nat) :: Symbol where
  ShowNatAux 'True hd 0 = hd `AppendSymbol` "0"
  ShowNatAux _ s n =
    CaseOrdering
      (CmpNat n 10)
      (ShowDigit n `AppendSymbol` s)
      (ShowNatAux 'True (ShowDigit (n `Mod` 10) `AppendSymbol` s) (n `Div` 10))
      (ShowNatAux 'True (ShowDigit (n `Mod` 10) `AppendSymbol` s) (n `Div` 10))

infixl 6 %+

(%+) :: SNat n -> SNat m -> SNat (n + m)
l %+ r =
  unsafeCoerce @Natural $
    demote l + demote r

infixl 6 %-

(%-) :: SNat n -> SNat m -> SNat (n - m)
l %- r =
  unsafeCoerce $
    demote l - demote r

(%<=?) :: SNat n -> SNat m -> SBool (n <=? m)
n %<=? m =
  if demote n <= demote m
    then unsafeCoerce STrue
    else unsafeCoerce SFalse

infix 4 %<=?

{- | Special deferring operator for builtin type-level ordering.

   See also: 'deferNatLeqWith'
-}
deferNatLeq ::
  forall n m x.
  (KnownNat n, KnownNat m) =>
  ((n <= m) => x) ->
  Either String x
deferNatLeq =
  deferNatLeqWith @n @m $
    ( "Type level inequality unsatisfied: "
        <> show (TN.natVal @n Proxy)
        <> " <= "
        <> show (TN.natVal @n Proxy)
    )

{- | Special deferring operator for builtin type-level ordering,
   with failure error message.

   See also: 'deferNatLeqWith'
-}
deferNatLeqWith ::
  forall n m x.
  (KnownNat n, KnownNat m) =>
  -- | Error message
  String ->
  ((n <= m) => x) ->
  Either String x
deferNatLeqWith errMsg act =
  case sKnownVal' @n %<=? sKnownVal' @m of
    STrue -> Right act
    SFalse -> Left errMsg

tnat :: QuasiQuoter
tnat =
  QuasiQuoter
    { quoteExp = \n ->
        [|sKnownVal' @($(parseNat n))|]
    , quotePat = \n ->
        let (theView, expectedP) = concreteNat n
         in viewP
              [|
                $theView
                  &&& ( ( \(_ :: SNat m) ->
                            unsafeCoerce (Equal @() @()) ::
                              Equality m $(parseNat n)
                        ) ::
                          forall m. SNat m -> Equality m $(parseNat n)
                      )
                  &&& ( ( \(_ :: SNat m) ->
                            unsafeCoerce (Equal @() @()) ::
                              Equality $(parseNat n) m
                        ) ::
                          forall m. SNat m -> Equality $(parseNat n) m
                      )
                |]
              [p|($expectedP, (Equal, Equal))|]
    , quoteDec = error "No definition for type natural"
    , quoteType = parseNat
    }
  where
    concreteNat :: String -> (ExpQ, PatQ)
    concreteNat inp =
      case readMaybe inp of
        Just n ->
          ( [|TL.natVal|]
          , litP $ integerL n
          )
        Nothing ->
          ([|(TL.natVal' @($(varT $ mkName inp)) ==)|], [p|True|])
    parseNat :: String -> TypeQ
    parseNat inp =
      case readMaybe @Natural inp of
        Just n -> litT $ numTyLit $ fromIntegral n
        Nothing -> [t|($(varT $ mkName inp) :: Nat)|]

caseNatLeq :: Natural -> TypeQ -> ExpQ -> ExpQ
caseNatLeq ub ty = flip (caseNatLeqWith ub ty) []

caseNatLeqWith :: Natural -> TypeQ -> ExpQ -> [(Natural, ExpQ)] -> ExpQ
caseNatLeqWith ub ty def cases = do
  when (any ((> ub) . fst) cases) $ do
    fail $ "Indices must be <= " <> show ub <> ", but got: " <> show (map fst cases)
  when (maybe False ((> ub) . fst) $ M.lookupMax dic) $
    fail $
      "Case out of range: " <> show (fst <$> M.lookupMax dic)
  [|
    let a = () :: (KnownNat $ty, $ty <= $(litT $ numTyLit $ fromIntegral ub)) => ()
     in a `seq` $body
    |]
  where
    dic = M.fromList cases
    body :: ExpQ
    body =
      caseE [|TL.natVal' @($ty) proxy#|] $
        map mkMatch [0 .. ub]
          ++ [match wildP (normalB [|error "caseNatLeqWith: Bug in GHC!"|]) []]
    mkMatch n =
      let reslE = fromMaybe def $ M.lookup n dic
          concNTy = litT $ numTyLit $ toInteger n
          bodyE =
            [|
              gcastWith
                (unsafeCoerce (Refl :: () :~: ()) :: $ty :~: $concNTy)
                $(reslE)
              |]
       in match (litP $ integerL $ toInteger n) (normalB bodyE) []
