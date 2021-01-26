{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Ccc.AsIntrinsified (intrinsify) where

import Ccc
import Ccc.Hom
import Ccc.Type
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Lam.Type as Lam
import Prelude hiding ((.), id)
import Data.Typeable ((:~:) (..))

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
  constant = k Lam.inferT
  cccIntrinsic x = E (cccIntrinsic x)

k :: Lam.KnownT a => Lam.ST a -> String -> String -> Expr f Unit (AsObject a)
k t pkg name = E $ case Map.lookup (pkg, name) intrinsics of
  Nothing -> constant pkg name
  Just (C h) -> case cast h Lam.inferT t of
    Nothing -> undefined
    Just x -> x

cast :: Hom f Unit (AsObject a) -> Lam.ST a -> Lam.ST b -> Maybe (Hom f Unit (AsObject b))
cast x t t' = do
  Refl <- Lam.eqT t t'
  pure x

data Constant = forall a. Lam.KnownT a => C (forall f. Hom f Unit (AsObject a))

intrinsics :: Map (String, String) Constant
intrinsics = Map.fromList [
  (("core", "add"),  C addIntrinsic),
  (("core", "multiply"),  C multiplyIntrinsic)
                          ]

addIntrinsic :: Hom f Unit (AsObject (Lam.U64 Lam.~> Lam.U64 Lam.~> Lam.U64))
addIntrinsic =
  zeta $ \x ->
  zeta $ \y ->
  add . lift x . y

multiplyIntrinsic :: Hom f Unit (AsObject (Lam.U64 Lam.~> Lam.U64 Lam.~> Lam.U64))
multiplyIntrinsic =
  zeta $ \x ->
  zeta $ \y ->
  mul . lift x . y

add :: Ccc hom => hom (U64 * U64) U64
add = cccIntrinsic AddIntrinsic

mul :: Ccc hom => hom (U64 * U64) U64
mul = cccIntrinsic MulIntrinsic
