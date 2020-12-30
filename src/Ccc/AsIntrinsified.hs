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

  lift (E x) = E (lift x)
  kappa f = E $ kappa $ \x' -> case f (E x') of
    E y -> y

  pass (E x) = E (pass x)
  zeta f = E $ zeta $ \x' -> case f (E x') of
    E y -> y

  u64 x = E (u64 x)
  constant pkg name = me where
    me = E $ case (typeOf me, pkg, name) of
      (Lam.SU64 Lam.:-> (Lam.SU64 Lam.:-> Lam.SU64), "core", "add") -> addIntrinsic
      _ -> constant pkg name

typeOf :: Lam.KnownT b => Expr f a (AsObject b) -> Lam.ST b
typeOf _ = Lam.inferT

addIntrinsic :: Hom f Unit (AsObject (Lam.U64 Lam.~> Lam.U64 Lam.~> Lam.U64))
addIntrinsic = zeta $ \x ->
               zeta $ \y ->
               ((add . lift x) . y)
