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
import Data.Text.Prettyprint.Doc

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
  show x = show $ evalState (view (fold x)) 0

newtype View (a :: T) = V { view :: State Int (Doc ()) }
instance Lam View where
  be x t f = V $ do
    x' <- view x
    v <- fresh
    body <- view (f (V $ pure v))
    let binder = sep [v, pretty ":", pretty (show t)]
    pure $ vsep[sep [x', pretty "be", binder, pretty "⇒"], body]

  lam t f = V $ do
    v <- fresh
    body <- view (f (V $ pure v))
    pure $ sep [pretty "λ", v, pretty ":", pretty (show t), pretty "⇒", body]

  f <*> x = V $ do
    f' <- view f
    x' <- view x
    pure $ parens $ sep [f', x']

  u64 n = V $ pure (pretty n)
  constant _ pkg name = V $ pure $ pretty (pkg ++ "/" ++ name)

fresh :: State Int (Doc ())
fresh = do
  n <- get
  put (n + 1)
  pure $ pretty "v" <> pretty n
