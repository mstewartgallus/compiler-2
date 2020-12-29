{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | Inline (kappa t f) `whereIs` x to f x sometimes (all the time rn)
module Ccc.Inline (inline) where

import Ccc
import Control.Category
import Ccc.Hom
import Ccc.Type
import Prelude hiding ((.), id)

inline :: Closed a b -> Closed a b
inline x = Closed (out (fold x))

data Expr f a b where
  E :: f a b -> Expr f a b
  Lift :: Ccc f => Expr f Unit a -> Expr f b (a * b)
  Kappa :: Ccc f => ST a -> (Expr f Unit a -> Expr f b c) -> Expr f (a * b) c

into :: f a b -> Expr f a b
into = E

out :: Expr f a b -> f a b
out expr = case expr of
  E x -> x
  Lift x -> lift (out x)
  Kappa t f -> kappa t (\x -> out (f (E x)))

instance Category f => Category (Expr f) where
  id = into id
  Kappa _ f . Lift x = f x
  f . g = into (out f . out g)

instance Ccc f => Ccc (Expr f) where
  unit = into unit

  lift = Lift
  kappa = Kappa

  pass x = into (pass (out x))
  zeta t f = into (zeta t $ \x -> out (f (into x)))

  u64 x = into (u64 x)
  constant t pkg name = into (constant t pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
