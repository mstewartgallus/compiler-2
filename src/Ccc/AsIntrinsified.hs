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
import Data.Type.Equality
import Type.Reflection
import Prelude hiding ((.), id)
import Data.Typeable ((:~:) (..))

intrinsify :: Term hom => hom a b -> Closed a b
intrinsify x = Closed (go (foldTerm x))

newtype Expr f (a :: T) (b :: T) = E { go :: f a b }

instance Ccc f => Ccc (Expr f) where
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

k :: (Ccc f, Lam.KnownT a) => TypeRep a -> String -> String -> Expr f Unit (AsObject a)
k t pkg name = E $ case Map.lookup (pkg, name) intrinsics of
  Nothing -> constant pkg name
  Just (C h) -> case cast h Lam.inferT t of
    Nothing -> undefined
    Just x -> x

cast :: Ccc f => f Unit (AsObject a) -> TypeRep a -> TypeRep b -> Maybe (f Unit (AsObject b))
cast x t t' = do
  Refl <- testEquality t t'
  pure x

data Constant f = forall a. Lam.KnownT a => C (f Unit (AsObject a))

intrinsics :: Ccc f => Map (String, String) (Constant f)
intrinsics = Map.fromList [
  (("core", "add"),  C addIntrinsic),
  (("core", "multiply"),  C multiplyIntrinsic)
                          ]

addIntrinsic :: Ccc f => f Unit (AsObject (Lam.U64 Lam.~> Lam.U64 Lam.~> Lam.U64))
addIntrinsic =
  zeta $ \x ->
  zeta $ \y ->
  add . lift x . y

multiplyIntrinsic :: Ccc f => f Unit (AsObject (Lam.U64 Lam.~> Lam.U64 Lam.~> Lam.U64))
multiplyIntrinsic =
  zeta $ \x ->
  zeta $ \y ->
  mul . lift x . y

add :: Ccc hom => hom (U64 * U64) U64
add = cccIntrinsic AddIntrinsic

mul :: Ccc hom => hom (U64 * U64) U64
mul = cccIntrinsic MulIntrinsic
