{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

-- | Simplify code of the sort unit . x to unit
module Ccc.RemoveDead (removeDead) where

import Ccc
import Control.Category
import Ccc.Hom
import Ccc.Type
import Prelude hiding ((.), id)

removeDead :: Closed a b -> Closed a b
removeDead x = Closed (out (fold x))

into :: k a b -> Expr k a b
into x = Pure x

out :: Ccc k => Expr k a b -> k a b
out x = case x of
  Pure x -> x
  Unit -> unit

data Expr k a b where
  Unit :: Expr k a Unit
  Pure :: k a b -> Expr k a b

instance Ccc k => Category (Expr k) where
  id = into id
  Unit . _ = Unit
  f . g = into (out f . out g)

instance Ccc k => Ccc (Expr k) where
  unit = Unit

  whereIs Unit _ = Unit
  whereIs f x = into (whereIs (out f) (out x))
  kappa t f = into (kappa t $ \x -> out (f (into x)))

  app f x = into (app (out f) (out x))
  zeta t f = into (zeta t $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant t pkg name = into (constant t pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
