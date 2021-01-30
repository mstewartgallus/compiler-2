{-# LANGUAGE GADTs #-}

-- | Simplify code of the sort unit . x to unit
module Ccc.RemoveDead (removeDead) where

import Ccc
import Ccc.Hom
import Ccc.Type
import Prelude hiding ((.), id)

removeDead :: Term hom => hom a b -> Closed a b
removeDead x = Closed (out (foldTerm x))

into :: k a b -> Expr k a b
into = Pure

out :: Expr k a b -> k a b
out x = case x of
  Pure x -> x
  Unit -> unit

data Expr k a b where
  Unit :: (Ccc k, KnownT a) => Expr k a Unit
  Pure :: k a b -> Expr k a b

instance Ccc k => Ccc (Expr k) where
  id = into id
  Unit . _ = Unit
  f . g = into (out f . out g)

  unit = Unit

  lift x = into (lift (out x))
  kappa f = into (kappa $ \x -> out (f (into x)))

  pass x = into (pass (out x))
  zeta f = into (zeta $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant pkg name = into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
