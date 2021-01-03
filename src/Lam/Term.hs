{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Lam.Term (fold, mkTerm, Term) where

import Lam
import Lam.Type
import Prelude hiding ((<*>))
import Data.Word (Word64)
import Control.Monad.State

mkTerm :: (forall t. (Num (t U64), Lam t) => t a) -> Term a
mkTerm = Term

newtype Term a = Term (forall x. Val x a)

fold :: Lam t => Term a -> t a
fold (Term x) = go x

-- | A simple high level intermediate language based off the simply
-- typed lambda calculus.  Uses parametric higher order abstract
-- syntax.  Evaluation is lazy.
data Val x a where
  Var :: KnownT a => x a -> Val x a
  Be :: (KnownT a, KnownT b) => Val x a -> (x a -> Val x b) -> Val x b
  Lam :: (KnownT a, KnownT b) => (x a -> Val x b) -> Val x (a ~> b)
  App :: (KnownT a, KnownT b) => Val x (a ~> b) -> Val x a -> Val x b
  U64 :: Word64 -> Val x U64
  Constant :: KnownT a => String -> String -> Val x a

instance Num (Val x U64) where
  x + y = constant "core" "add" <*> x <*> y
  x - y = constant "core" "subtract" <*> x <*> y
  x * y = constant "core" "multiply" <*> x <*> y

instance Lam (Val x) where
  lam f = Lam (f . Var)
  (<*>) = App

  be x f = Be x (f . Var)

  u64 = U64
  constant = Constant

go :: Lam t => Val t a -> t a
go x = case x of
  Var v -> v
  Be x f -> be (go x) (go . f)
  Lam f -> lam (go . f)
  App f x -> go f <*> go x
  U64 n -> u64 n
  Constant pkg name -> constant pkg name
