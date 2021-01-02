{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | Convert pass x . zeta t f to kappa t f . push x
module Ccc.ZetaToKappa (zetaToKappa) where

import Ccc
import Ccc.Hom
import Ccc.Type
import Prelude hiding ((.), id)

zetaToKappa :: Closed a b -> Closed a b
zetaToKappa x = Closed (out (fold x))

data Expr f a b where
  E :: f a b -> Expr f a b
  Zeta :: (KnownT a, KnownT b, KnownT c, Ccc f) => (Expr f Unit a -> Expr f b c) -> Expr f b (a ~> c)

into :: f a b -> Expr f a b
into = E

out :: Expr f a b -> f a b
out expr = case expr of
  E x -> x
  Zeta f -> zeta (\x -> out (f (E x)))

instance Ccc f => Ccc (Expr f) where
  id = into id
  f . g = into (out f . out g)

  unit = into unit

  lift f x = into (lift (out f) (out x))
  kappa f = into (kappa $ \x -> out (f (into x)))

  pass (Zeta f) x = f x
  pass f x = into (pass (out f) (out x))
  zeta = Zeta

  u64 x = into (u64 x)
  constant pkg name = into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
