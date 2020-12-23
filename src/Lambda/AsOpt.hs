{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Lambda.AsOpt (Expr, opt) where

import Lambda
import Control.Category
import Lambda.HasExp
import Lambda.HasUnit
import Lambda.HasProduct
import Lambda.HasSum
import Lambda.Type
import qualified Hoas.Type as Hoas
import qualified Lambda.AsRepeat as AsRepeat
import Prelude hiding ((.), id, curry, uncurry, Monad (..), Either (..))

opt :: Expr f a b -> f a b
opt (E x) = AsRepeat.repeat 20 x

newtype Expr f (a :: T) (b :: T) = E (AsRepeat.Expr f a b)

instance Category f => Category (Expr f) where
  id = E id
  E f . E g = E (f . g)

instance HasUnit f => HasUnit (Expr f) where
  unit = E unit

instance HasProduct f => HasProduct (Expr f) where
  lift (E f) = E (lift f)
  kappa t f = E $ kappa t $ \x' -> case f (E x') of
    E y -> y

instance HasExp f => HasExp (Expr f) where
  pass (E x) = E (pass x)
  zeta t f = E $ zeta t $ \x' -> case f (E x') of
    E y -> y

instance HasSum f => HasSum (Expr f) where
  absurd = E absurd
  E f ||| E g = E (f ||| g)
  left = E left
  right = E right

instance Lambda f => Lambda (Expr f) where
  u64 x = E (u64 x)
  constant t pkg name = E $ case (t, pkg, name) of
    (Hoas.SU64 Hoas.:-> (Hoas.SU64 Hoas.:-> Hoas.SU64), "core", "add") -> addIntrinsic
    _ -> constant t pkg name

addIntrinsic :: Lambda f => f Unit (AsObject (Hoas.U64 Hoas.~> Hoas.U64 Hoas.~> Hoas.U64))
addIntrinsic = zeta inferT $ \x ->
               zeta inferT $ \y ->
               add . lift x . y
