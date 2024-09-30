{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.TypeLevel.BinTree (BinTree (..), Bin, Val, Stop, MkBin, ToList, FromList) where

import Data.TypeLevel.List
import GHC.Generics
import Type.Reflection

data BinTree a
  = Bin Nat (BinTree a) (BinTree a)
  | Val a
  | Stop
  deriving (Typeable, Generic)

type Val = 'Val

type Bin = 'Bin

type Stop = 'Stop

type family Size (tree :: BinTree a) :: Nat where
  Size 'Stop = 0
  Size ('Val _) = 1
  Size (Bin n _ _) = n

type MkBin l r = Bin (Size l + Size r) l r

type FromList as = FromListAux (Map 'Val as)

type family FromListAux (as :: [BinTree a]) :: BinTree a where
  FromListAux '[] = 'Stop
  FromListAux '[t] = t
  FromListAux xs =
    FromListAux (MkBins xs)

type family MkBins (trs :: [BinTree a]) :: [BinTree a] where
  MkBins '[] = '[]
  MkBins '[t] = '[t]
  MkBins (x ': y ': xs) =
    MkBin x y ': MkBins xs

type ToList tree = ToListAux '[] tree

type family ToListAux (acc :: [a]) (tree :: BinTree a) :: [a] where
  ToListAux acc 'Stop = acc
  ToListAux acc ('Val a) = a ': acc
  ToListAux acc ('Bin _ l r) =
    ToListAux (ToListAux acc r) l
