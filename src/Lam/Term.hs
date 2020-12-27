{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Lam.Term (fold, Term, Closed (..)) where

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

newtype Closed a = Closed (forall x. Term x a)

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
  show x = evalState (view (fold x) 0) 0

newtype View (a :: T) = V { view :: Int -> State Int String }
instance Lam View where
  be x t f = V $ \p -> do
    x' <- view x beprec
    v <- fresh
    body <- view (f (V $ \_ -> pure v)) beprec
    pure $ paren (p >= beprec) $ x' ++ " be " ++ v ++ ": " ++ show t ++ ". " ++ body

  lam t f = V $ \p -> do
    v <- fresh
    body <- view (f (V $ \_ -> pure v)) lamprec
    pure $ paren (p >= lamprec) $ "λ " ++ v ++ ": " ++ show t ++ ". " ++ body

  f <*> x = V $ \p -> do
    f' <- view f appprec
    x' <- view x appprec
    pure $ paren (p >= appprec) $ f' ++ " " ++ x'

  u64 n = V $ \_ -> pure (show n)
  constant _ pkg name = V $ \_ -> pure (pkg ++ "/" ++ name)

fresh :: State Int String
fresh = do
  n <- get
  put (n + 1)
  pure ("v" ++ show n)

paren :: Bool -> String -> String
paren True str = "(" ++ str ++ ")"
paren _ str = str

appprec :: Int
appprec = 9

lamprec :: Int
lamprec = 0

beprec :: Int
beprec = 0
