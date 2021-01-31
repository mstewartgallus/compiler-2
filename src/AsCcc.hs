{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module AsCcc (asCcc) where

import Ccc
import Ccc.Type
import Dict
import qualified Lam as Lam
import qualified Lam.Type as Lam
import Prelude hiding (id, (.))

asCcc :: Lam.Term t => t a -> Closed Unit (AsObject a)
asCcc x = Closed (go (Lam.foldTerm x))

newtype Closed a b = Closed (forall k. Ccc k => k a b)

instance Term Closed where
  foldTerm (Closed p) = p

newtype V k a = V {go :: Ccc k => k Unit (AsObject a)}

instance Ccc k => Lam.Lam (V k) where
  be = be' Lam.inferT Lam.inferT
  lam = lam' Lam.inferT Lam.inferT
  (<*>) = pass' Lam.inferT Lam.inferT

  u64 n = V (u64 n)
  constant pkg name = V (constant pkg name)

be' :: Foo Bar a -> ObjectOf b -> V k a -> (V k a -> V k b) -> V k b
be' (Foo Bar) (ObjectOf Dict) (V x) f = V $ kappa (\x' -> go (f (V x'))) . lift x

lam' :: ObjectOf a -> ObjectOf b -> (V k a -> V k b) -> V k (a Lam.~> b)
lam' (ObjectOf Dict) (ObjectOf Dict) f = V $ zeta (\x -> go (f (V x)))

pass' :: ObjectOf a -> ObjectOf b -> V k (a Lam.~> b) -> V k a -> V k b
pass' (ObjectOf Dict) (ObjectOf Dict) (V f) (V x) = V (pass x . f)
