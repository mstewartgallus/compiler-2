{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Lam (Closed (..), Term (..), letBe, be, lam, add, u64, constant, (<*>)) where

import Control.Category
import Control.Monad.State
import Data.Word (Word64)
import Lam.Type
import Prelude hiding (id, (.), (<*>))

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

u64 :: Word64 -> Term x U64
u64 = U64

constant :: ST a -> String -> String -> Term x a
constant = Constant

lam :: ST a -> (Term x a -> Term x b) -> Term x (a ~> b)
lam t f = Lam t (f . Var)

(<*>) :: Term x (a ~> b) -> Term x a -> Term x b
(<*>) = App

be :: Term x a -> ST a -> (Term x a -> Term x b) -> Term x b
be x t f = Be x t (f . Var)

add :: Term x (U64 ~> U64 ~> U64)
add = Constant inferT "core" "add"

letBe :: KnownT a => Term x a -> (Term x a -> Term x b) -> Term x b
letBe x f = be x inferT f

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
