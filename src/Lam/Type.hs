{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeOperators #-}

module Lam.Type (eqT, KnownT, Tagged (..), inferT, toKnownT, ST (..), T, type (~>), type Unit, type U64) where

import Dict
import Type.Reflection
import Data.Type.Equality
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

data ST a = KnownT a => ST

instance Tagged ST where
  unitTag = ST
  u64Tag = ST
  expTag ST ST = ST

toKnownT :: ST a -> Dict (KnownT a)
toKnownT ST = Dict

instance Tagged TypeRep where
  unitTag = typeRep
  u64Tag = typeRep
  expTag a b = a `withTypeable` (b `withTypeable` typeRep)

trep :: ST a -> TypeRep a
trep ST = inferT

eqT :: ST a -> ST b -> Maybe (a :~: b)
eqT x y = testEquality (trep x) (trep y)
