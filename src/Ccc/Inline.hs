{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | Inline kappa t f . push x to f x sometimes (all the time rn)
module Ccc.Inline (inline) where

import Ccc
import Ccc.Hom
import Ccc.Type
import Prelude hiding ((.), id)

inline :: Closed a b -> Closed a b
inline x = Closed (out (fold x))

data Expr f a b where
  E :: f a b -> Expr f a b
  Kappa :: (KnownT a, KnownT b, KnownT c, Ccc f) => (Expr f Unit a -> Expr f b c) -> Expr f (a * b) c

into :: f a b -> Expr f a b
into = E

out :: Expr f a b -> f a b
out expr = case expr of
  E x -> x
  Kappa f -> kappa (\x -> out (f (E x)))

instance Ccc f => Ccc (Expr f) where
  id = into id
  f . g = into (out f . out g)

  unit = into unit

  lift (Kappa f) x = f x
  lift f x = into (lift (out f) (out x))
  kappa = Kappa

  pass f x = into (pass (out f) (out x))
  zeta f = into (zeta $ \x -> out (f (into x)))

  u64 x = into (u64 x)
  constant pkg name = into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
