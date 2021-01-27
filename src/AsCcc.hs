{-# LANGUAGE TypeOperators #-}

module AsCcc (asCcc) where

import Ccc
import Ccc.Hom
import Ccc.Type
import Dict
import qualified Lam as Lam
import qualified Lam.Type as Lam
import Prelude hiding (id, (.))

asCcc :: Lam.Term t => t a -> Closed Unit (AsObject a)
asCcc x = Closed (go (Lam.foldTerm x))

newtype V k a = V {go :: Hom k Unit (AsObject a)}

instance Lam.Lam (V k) where
  be = be' Lam.inferT Lam.inferT
  lam = lam' Lam.inferT Lam.inferT
  (<*>) = pass' Lam.inferT Lam.inferT

  u64 n = V (u64 n)
  constant pkg name = V (constant pkg name)

be' :: ObjectOf KnownDict a -> ObjectOf KnownDict b -> V k a -> (V k a -> V k b) -> V k b
be' a b (V x) f = case (toKnownT (asObject a), toKnownT (asObject b)) of
  (Dict, Dict) -> V $ kappa (\x' -> go (f (V x'))) . lift x

lam' :: ObjectOf KnownDict a -> ObjectOf KnownDict b -> (V k a -> V k b) -> V k (a Lam.~> b)
lam' a b f = case (toKnownT (asObject a), toKnownT (asObject b)) of
  (Dict, Dict) -> V $ zeta (\x -> go (f (V x)))

pass' :: ObjectOf KnownDict a -> ObjectOf KnownDict b -> V k (a Lam.~> b) -> V k a -> V k b
pass' a b (V f) (V x) = case (toKnownT (asObject a), toKnownT (asObject b)) of
  (Dict, Dict) -> V (pass x . f)
