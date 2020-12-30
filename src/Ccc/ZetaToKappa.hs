{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | Convert (zeta t f) `app` x to (kappa t f) `whereIs` x
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
  Zeta :: (KnownT a, KnownT b, KnownT c, Ccc f) => ST a -> (Expr f Unit a -> Expr f b c) -> Expr f b (a ~> c)

into :: f a b -> Expr f a b
into = E

out :: Expr f a b -> f a b
out expr = case expr of
  E x -> x
  Pass x -> pass (out x)
  Zeta t f -> zeta t (\x -> out (f (E x)))

instance Ccc f => Ccc (Expr f) where
  id = into id
  Pass x . Zeta t f = into (kappa t (\x -> out (f (into x))) . lift (out x))
  f . g = into (out f . out g)

  unit = into unit

  lift x = into (lift (out x))
  kappa t f = into (kappa t $ \x -> out (f (into x)))

  pass = Pass
  zeta = Zeta

  u64 x = into (u64 x)
  constant t pkg name = into (constant t pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
