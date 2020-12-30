{-# LANGUAGE GADTs #-}

module AsCcc (asCcc) where

import Ccc
import Ccc.Hom
import Ccc.Type
import qualified Lam as Lam
import qualified Lam.Term as Lam
import qualified Lam.Type as Lam
import Prelude hiding (id, (.))

asCcc :: Lam.Closed a -> Closed Unit (AsObject a)
asCcc x = Closed (go (Lam.fold x))

newtype V k a = V {go :: Hom k Unit (AsObject a)}

instance Lam.Lam (V k) where
  be (V x) f = V $ kappa (asObject Lam.inferT) (\x' -> go (f (V x'))) . lift x
  lam f = V $ zeta (asObject Lam.inferT) (\x -> go (f (V x)))
  V f <*> V x = V (pass x . f)

  u64 n = V (u64 n)
  constant pkg name = V (constant Lam.inferT pkg name)
