{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Ccc.AsIntrinsified (intrinsify) where

import Ccc
import Ccc.Hom
import Control.Category
import Ccc.HasExp
import Ccc.HasUnit
import Ccc.HasProduct
import Ccc.Type
import qualified Lam.Type as Lam
import Prelude hiding ((.), id, curry, uncurry, Monad (..), Either (..))

intrinsify :: Closed a b -> Closed a b
intrinsify x = Closed (go (fold x))

newtype Expr f (a :: T) (b :: T) = E { go :: Hom f a b }

instance Category (Expr f) where
  id = E id
  E f . E g = E (f . g)

instance HasUnit (Expr f) where
  unit = E unit

instance HasProduct (Expr f) where
  whereIs (E f) (E x) = E (whereIs f x)
  kappa t f = E $ kappa t $ \x' -> case f (E x') of
    E y -> y

instance HasExp (Expr f) where
  app (E f) (E x) = E (app f x)
  zeta t f = E $ zeta t $ \x' -> case f (E x') of
    E y -> y

instance Ccc (Expr f) where
  u64 x = E (u64 x)
  constant t pkg name = E $ case (t, pkg, name) of
    (Lam.SU64 Lam.:-> (Lam.SU64 Lam.:-> Lam.SU64), "core", "add") -> addIntrinsic
    _ -> constant t pkg name

addIntrinsic :: Hom f Unit (AsObject (Lam.U64 Lam.~> Lam.U64 Lam.~> Lam.U64))
addIntrinsic = zeta inferT $ \x ->
               zeta inferT $ \y ->
               ((add `whereIs` x) . y)
