{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Lam.Term (fold, Term, Closed (..)) where

import Lam
import Pretty
import Lam.Type
import Prelude hiding ((<*>))
import Data.Word (Word64)
import Control.Monad.State
import Data.Text.Prettyprint.Doc

-- | A simple high level intermediate language based off the simply
-- typed lambda calculus.  Uses parametric higher order abstract
-- syntax.  Evaluation is lazy.
data Term x a where
  Var :: KnownT a => x a -> Term x a
  Be :: (KnownT a, KnownT b) => Term x a -> (x a -> Term x b) -> Term x b
  Lam :: (KnownT a, KnownT b) => (x a -> Term x b) -> Term x (a ~> b)
  App :: (KnownT a, KnownT b) => Term x (a ~> b) -> Term x a -> Term x b
  U64 :: Word64 -> Term x U64
  Constant :: KnownT a => String -> String -> Term x a

newtype Closed a = Closed (forall x. Term x a)

instance Num (Term x U64) where
  x + y = constant "core" "add" <*> x <*> y
  x - y = constant "core" "subtract" <*> x <*> y
  x * y = constant "core" "multiply" <*> x <*> y

instance Lam (Term x) where
  lam f = Lam (f . Var)
  (<*>) = App

  be x f = Be x (f . Var)

  u64 = U64
  constant = Constant

fold :: Lam t => Closed a -> t a
fold (Closed x) = go x

go :: Lam t => Term t a -> t a
go x = case x of
  Var v -> v
  Be x f -> be (go x) (go . f)
  Lam f -> lam (go . f)
  App f x -> go f <*> go x
  U64 n -> u64 n
  Constant pkg name -> constant pkg name

instance PrettyProgram (Closed a) where
  prettyProgram x = evalState (view (fold x) 0) 0

appPrec :: Int
appPrec = 10

lamPrec :: Int
lamPrec = 9

bePrec :: Int
bePrec = 8

paren :: Bool -> Doc Style -> Doc Style
paren x = if x then parens else id

newtype View (a :: T) = V { view :: Int -> State Int (Doc Style) }

instance Lam View where
  be = be' inferT
  lam = lam' inferT

  f <*> x = V $ \p -> do
    f' <- view f (appPrec + 1)
    x' <- view x (appPrec + 1)
    pure $ paren (p > appPrec) $ sep [f', x']

  u64 n = V $ \_ -> pure (pretty n)
  constant pkg name = V $ \_ -> pure $ pretty (pkg ++ "/" ++ name)

be' :: ST a -> View a -> (View a -> View b) -> View b
be' t x f = V $ \p -> do
  x' <- view x (bePrec + 1)
  v <- fresh
  body <- view (f (V $ \_ -> pure v)) (bePrec + 1)
  let binder = sep [v, keyword (pretty ":"), prettyProgram t]
  pure $ paren (p > bePrec) $ vsep [sep [x', keyword (pretty "be"), binder, keyword (pretty "⇒")], body]

lam' :: ST a -> (View a -> View b) -> View (a ~> b)
lam' t f = V $ \p -> do
    v <- fresh
    body <- view (f (V $ \_ -> pure v)) (lamPrec + 1)
    pure $ paren (p > lamPrec) $ sep [keyword (pretty "λ"), v, keyword (pretty ":"), prettyProgram t, keyword (pretty "⇒"), body]

fresh :: State Int (Doc Style)
fresh = do
  n <- get
  put (n + 1)
  pure $ variable (pretty "v" <> pretty n)
