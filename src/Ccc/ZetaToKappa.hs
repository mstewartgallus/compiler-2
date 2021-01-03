{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | Convert pass x . zeta f to kappa f . push x
module Ccc.ZetaToKappa (zetaToKappa) where

import Ccc
import Ccc.Hom
import Ccc.Type
import Prelude hiding ((.), id)

zetaToKappa :: Closed a b -> Closed a b
zetaToKappa x = Closed (out (fold x))

data Expr f a b where
  E :: f a b -> Expr f a b
  Pass :: (KnownT a, KnownT b, Ccc f) => Expr f Unit a -> Expr f (a ~> b) b
  Zeta :: (KnownT a, KnownT b, KnownT c, Ccc f) => (Expr f Unit a -> Expr f b c) -> Expr f b (a ~> c)

into :: f a b -> Expr f a b
into = E

out :: Expr f a b -> f a b
out expr = case expr of
  E x -> x
  Pass x -> pass (out x)
  Zeta f -> zeta (\x -> out (f (E x)))

instance Ccc f => Ccc (Expr f) where
  id = into id
  Pass x . Zeta f = f x
  f . g = into (out f . out g)

  unit = into unit

  lift x = into (lift (out x))
  kappa f = into (kappa $ \x -> out (f (into x)))

  pass = Pass
  zeta = Zeta

  u64 x = into (u64 x)
  constant pkg name = into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
