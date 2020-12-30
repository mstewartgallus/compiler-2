{-# LANGUAGE TypeOperators #-}

module AsCcc (asCcc) where

import Ccc
import Ccc.Hom
import Ccc.Type
import Dict
import qualified Lam as Lam
import qualified Lam.Term as Lam
import qualified Lam.Type as Lam
import Prelude hiding (id, (.))

asCcc :: Lam.Closed a -> Closed Unit (AsObject a)
asCcc x = Closed (go (Lam.fold x))

newtype V k a = V {go :: Hom k Unit (AsObject a)}

typeOf :: Lam.KnownT a => V k a -> Lam.ST a
typeOf _ = Lam.inferT

argOf :: Lam.KnownT a => (V k a -> V k b) -> Lam.ST a
argOf _ = Lam.inferT

resultOf :: Lam.KnownT b => (V k a -> V k b) -> Lam.ST b
resultOf _ = Lam.inferT

resultOf' :: Lam.KnownT b => V k (a Lam.~> b) -> Lam.ST b
resultOf' _ = Lam.inferT

instance Lam.Lam (V k) where
  be (V x) f =
    let t = asObject (argOf f)
     in case (toKnownT t, toKnownT (asObject (resultOf f))) of
          (Dict, Dict) -> V $ kappa t (\x' -> go (f (V x'))) . lift x
  lam f =
    let a = asObject (argOf f)
     in case (toKnownT a, toKnownT (asObject (resultOf f))) of
          (Dict, Dict) -> V $ zeta a (\x -> go (f (V x)))
  f'@(V f) <*> x'@(V x) = case (toKnownT (asObject (typeOf x')), toKnownT (asObject (resultOf' f'))) of
    (Dict, Dict) -> V (pass x . f)

  u64 n = V (u64 n)
  constant pkg name = V (constant Lam.inferT pkg name)
