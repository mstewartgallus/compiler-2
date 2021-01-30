{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- | Convert pass x . zeta f to kappa f . push x
module Ccc.ZetaToKappa (zetaToKappa) where

import Ccc
import Ccc.Type
import Prelude hiding ((.), id)

zetaToKappa :: Term hom => hom a b -> Closed a b
zetaToKappa x = Closed (out (foldTerm x))

newtype Closed a b = Closed (forall k. Ccc k => Expr k a b)
instance Term Closed where
  foldTerm (Closed p) = out p

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
  Pass x . Zeta f = kappa f . lift x
  f . g = into (out f . out g)

  unit = into unit

  lift x = into (lift (out x))
  kappa f = into (kappa $ \x -> out (f (into x)))

  pass = Pass
  zeta = Zeta

  u64 x = into (u64 x)
  constant pkg name = into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
