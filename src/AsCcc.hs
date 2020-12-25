{-# LANGUAGE GADTs #-}

module AsCcc (asCcc) where

import Ccc
import Ccc.HasExp
import Ccc.HasProduct
import Ccc.Hom
import Ccc.Type
import Control.Category
import qualified Lam as Lam
import qualified Lam.Term as Lam
import Prelude hiding (id, (.))

asCcc :: Lam.Closed a -> Closed Unit (AsObject a)
asCcc x = Closed (go (Lam.fold x))

newtype V k a = V {go :: Hom k Unit (AsObject a)}

instance Lam.Lam (V k) where
  be (V x) t f = V $ lift x >>> kappa (asObject t) (\x' -> go (f (V x')))
  lam t f = V $ zeta (asObject t) (\x -> go (f (V x)))
  V f <*> V x = V (pass x . f)

  u64 n = V (u64 n)
  constant t pkg name = V (constant t pkg name)
