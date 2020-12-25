{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Lam.Term (fold, Term (..), Closed (..)) where

import Lam
import Lam.Type
import Prelude hiding ((<*>))
import Data.Word (Word64)
import Control.Monad.State

-- | A simple high level intermediate language based off the simply
-- typed lambda calculus.  Uses parametric higher order abstract
-- syntax.  Evaluation is lazy.
data Term x a where
  Var :: x a -> Term x a
  Be :: Term x a -> ST a -> (x a -> Term x b) -> Term x b
  Lam :: ST a -> (x a -> Term x b) -> Term x (a ~> b)
  App :: Term x (a ~> b) -> Term x a -> Term x b
  U64 :: Word64 -> Term x U64
  Constant :: ST a -> String -> String -> Term x a

newtype Closed a = Closed {interpret :: forall x. Term x a}

instance Lam (Term x) where
  lam t f = Lam t (f . Var)
  (<*>) = App

  be x t f = Be x t (f . Var)

  u64 = U64
  constant = Constant

fold :: Lam t => Closed a -> t a
fold (Closed x) = go x

go :: Lam t => Term t a -> t a
go x = case x of
  Var v -> v
  Be x t f -> be (go x) t (go . f)
  Lam t f -> lam t (go . f)
  App f x -> go f <*> go x
  U64 n -> u64 n
  Constant t pkg name -> constant t pkg name

instance Show (Closed a) where
  show (Closed x) = evalState (view x) 0

newtype View (a :: T) = V String

view :: Term View a -> State Int String
view x = case x of
  Var (V s) -> pure s
  Be x t f -> do
    v <- fresh
    x' <- view x
    body <- view (f (V v))
    pure (x' ++ " be " ++ v ++ ": " ++ show t ++ ". " ++ body)
  Lam t f -> do
    v <- fresh
    body <- view (f (V v))
    pure ("(λ " ++ v ++ ": " ++ show t ++ ". " ++ body ++ ")")
  App f x -> do
    f' <- view f
    x' <- view x
    pure $ "(" ++ f' ++ " " ++ x' ++ ")"
  U64 n -> pure (show n)
  Constant _ pkg name -> pure (pkg ++ "/" ++ name)

fresh :: State Int String
fresh = do
  n <- get
  put (n + 1)
  pure ("v" ++ show n)
