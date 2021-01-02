{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Ccc.AsIntrinsified (intrinsify) where

import Ccc
import Ccc.Hom
import Ccc.Type
import qualified Lam.Type as Lam
import Prelude hiding ((.), id)

intrinsify :: Closed a b -> Closed a b
intrinsify x = Closed (go (fold x))

newtype Expr f (a :: T) (b :: T) = E { go :: Hom f a b }

instance Ccc (Expr f) where
  id = E id
  E f . E g = E (f . g)

  unit = E unit

  lift (E f) (E x) = E (lift f x)
  kappa f = E $ kappa $ \x' -> case f (E x') of
    E y -> y

  pass (E f) (E x) = E (pass f x)
  zeta f = E $ zeta $ \x' -> case f (E x') of
    E y -> y

  u64 x = E (u64 x)
  constant = k Lam.inferT
  cccIntrinsic x = E (cccIntrinsic x)

k :: Lam.KnownT a => Lam.ST a -> String -> String -> Expr f Unit (AsObject a)
k (Lam.SU64 Lam.:-> (Lam.SU64 Lam.:-> Lam.SU64)) "core" "add" = E addIntrinsic
k _ pkg name = E (constant pkg name)

addIntrinsic :: Hom f Unit (AsObject (Lam.U64 Lam.~> Lam.U64 Lam.~> Lam.U64))
addIntrinsic = zeta $ \x ->
               zeta $ \y ->
               ((lift add x) . y)
