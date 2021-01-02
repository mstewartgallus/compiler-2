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

instance Lam.Lam (V k) where
  be = be' Lam.inferT Lam.inferT
  lam = lam' Lam.inferT Lam.inferT
  (<*>) = pass' Lam.inferT Lam.inferT

  u64 n = V (u64 n)
  constant pkg name = V (constant pkg name)

be' :: Lam.ST a -> Lam.ST b -> V k a -> (V k a -> V k b) -> V k b
be' a b (V x) f = case (toKnownT (asObject a), toKnownT (asObject b)) of
  (Dict, Dict) -> V $ lift (kappa (\x' -> go (f (V x')))) x

lam' :: Lam.ST a -> Lam.ST b -> (V k a -> V k b) -> V k (a Lam.~> b)
lam' a b f = case (toKnownT (asObject a), toKnownT (asObject b)) of
  (Dict, Dict) -> V $ zeta (\x -> go (f (V x)))

pass' :: Lam.ST a -> Lam.ST b -> V k (a Lam.~> b) -> V k a -> V k b
pass' a b (V f) (V x) = case (toKnownT (asObject a), toKnownT (asObject b)) of
  (Dict, Dict) -> V (pass f x)
