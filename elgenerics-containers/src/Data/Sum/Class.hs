{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Sum.Class (
  HasSummand (..),
  inject,
  project,
  ginject,
  SumPath,
  Path' (..),
  KnownPath (..),
) where

import Data.Maybe
import Data.Proxy
import Data.TypeLevel.Maybe
import Data.TypeLevel.Path
import GHC.TypeLits

inject :: (HasSummand c a) => c -> a
{-# INLINE [1] inject #-}
inject = inject'

project :: (HasSummand c a) => a -> Maybe c
{-# INLINE [1] project #-}
project = project'

{-# RULES
"project/inject" forall x.
  project (inject x) =
    Just x
"inject/project" forall x.
  inject (fromJust (project x)) =
    x
  #-}

inject0 :: SumPath c f -> c -> f ()
inject0 K c = K1 c
inject0 (M f) c = M1 $ inject0 f c
inject0 (InL f) c = L1 $ inject0 f c
inject0 (InR g) c = R1 $ inject0 g c

project0 :: SumPath c f -> f () -> Maybe c
project0 K (K1 c) = Just c
project0 (M p) (M1 f) = project0 p f
project0 (InL p) (L1 f) = project0 p f
project0 (InR p) (R1 f) = project0 p f
project0 _ _ = Nothing

ginject :: (Generic a) => SumPath c (Rep a) -> c -> a
ginject pth c = to $ inject0 pth c

gproject :: (Generic a) => SumPath c (Rep a) -> a -> Maybe c
gproject pth = project0 pth . from

{- | 値コンストラクタを持つか？

   Generic を使ったデフォルト実装では、
   自動でコンストラクタを探してきて inject する。

   __注__: 一旦 @'Generic'@ を介して変換するので、
   @'inject'@, @'project'@ 共に \(O(\log n)\)
   時間計算量が掛かる（ここで \(n\) はデータ構築子の数）。

   構築子が少なければあまり影響はないが、そうではない場合は
   個別にちゃんと @'inject'@ を実装してやること。
-}
class HasSummand c a where
  inject' :: c -> a
  default inject' ::
    ( Generic a
    , KnownPath SumOnly c (Rep a) (ConsPath c a)
    ) =>
    c ->
    a
  inject' = ginject (getPath (Proxy @c) (Proxy @a))

  project' :: a -> Maybe c
  default project' ::
    ( Generic a
    , KnownPath SumOnly c (Rep a) (ConsPath c a)
    ) =>
    a ->
    Maybe c
  project' = gproject (getPath (Proxy @c) (Proxy @a))

instance {-# OVERLAPPING #-} HasSummand c c where
  inject' = id
  project' = Just

getPath ::
  forall c a pxy.
  (KnownPath SumOnly c (Rep a) (ConsPath c a)) =>
  pxy c ->
  pxy a ->
  SumPath c (Rep a)
getPath _ _ = pathVal (Proxy :: Proxy (ConsPath c a))

type ConsPath ::
  forall c -> forall a -> SumPath c (Rep a)
type family ConsPath c a :: SumPath c (Rep a) where
  ConsPath c a =
    FromJust
      ( 'Text "A type `"
          ':<>: 'ShowType a
          ':<>: 'Text "' doesn't have unary constructor with type `"
          ':<>: 'ShowType c
          ':<>: 'Text "'"
      )
      (PositionOf SumOnly c a)
