{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Lam.Type (eqT, KnownT, Tagged (..), inferT, toKnownT, ST (..), T, type (~>), type Unit, type U64) where

import Dict
import Type.Reflection
import Data.Typeable ((:~:) (..))

type (~>) = 'Exp

type U64 = 'U64
type Unit = 'Unit

infixr 9 ~>

data T = Unit | U64 | Exp T T

class Typeable a => KnownT a where
  inferT :: Tagged t => t a

instance KnownT 'Unit where
  inferT = unitTag

instance KnownT 'U64 where
  inferT = u64Tag

instance (KnownT a, KnownT b) => KnownT ('Exp a b) where
  inferT = expTag inferT inferT

class Tagged t where
  unitTag :: t Unit
  u64Tag :: t U64
  expTag :: t a -> t b -> t (a ~> b)

data ST a where
  SUnit :: ST Unit
  SU64 :: ST U64
  (:->) :: ST a -> ST b -> ST (a ~> b)

instance Tagged ST where
  unitTag = SUnit
  u64Tag = SU64
  expTag = (:->)

toKnownT :: ST a -> Dict (KnownT a)
toKnownT x = case x of
  SU64 -> Dict
  SUnit -> Dict
  x :-> y -> case (toKnownT x, toKnownT y) of
    (Dict, Dict) -> Dict

eqT :: ST a -> ST b -> Maybe (a :~: b)
eqT x y = case (x, y) of
  (SU64, SU64) -> pure Refl
  (SUnit, SUnit) -> pure Refl
  (a :-> b, a' :-> b') -> do
    Refl <- eqT a a'
    Refl <- eqT b b'
    pure Refl
