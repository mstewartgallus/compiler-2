{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.AsView (Stack, view) where

import Cbpv
import Control.Category
import Control.Monad.State
import Cbpv.Sort
import Prelude hiding ((.), id)

newtype Stk (a :: Algebra) (b :: Algebra) = K (State Int String)

newtype Cde (a :: Set) (b :: Set) = C (State Int String)

view :: Cde a b -> String
view (C v) = evalState v 0

instance Category Stk where
  id = K $ pure "pass"
  K f . K g = K $ pure (\f' g' -> g' ++ ";\n" ++ f') <*> f <*> g

instance Category Cde where
  id = C $ pure "id"
  C f . C g = C $ pure (\f' g' -> f' ++ " ∘ " ++ g') <*> f <*> g

indent = unlines . map ("\t" ++) . lines

instance Code Cde where
  unit = C $ pure "unit"

  lift (C f) = C $ pure (\f' -> "(lift " ++ f' ++ ")") <*> f
  kappa _ f = C $ do
    v <- fresh
    let C body = f (C $ pure v)
    pure (\body' -> "kappa " ++ v ++ ".\n" ++ body' ++ "") <*> body

  absurd = C $ pure "absurd"
  C f ||| C g = C $ pure (\f' g' -> "[" ++ f' ++ " , " ++ g' ++ "]") <*> f <*> g
  left = C $ pure "i₁"
  right = C $ pure "i₂"

instance Stack Stk where

instance Cbpv Stk Cde where
  return (C f) = K $ pure (\f' -> "return " ++ f' ++ "") <*> f

  thunk (K f) = C $ pure (\f' -> "thunk {" ++ indent ("\n" ++ f')  ++ "}") <*> f
  force (C f) = K $ pure (\f' -> "force " ++ f' ++ "") <*> f

  pass (C f) = K $ pure (\f' -> "(pass " ++ f' ++ ")") <*> f
  push (C f) = K $ pure (\f' -> "(push " ++ f' ++ ")") <*> f

  zeta t f = K $ do
    v <- fresh
    let K body = f (C $ pure v)
    body' <- body
    pure (\body' -> "(ζ" ++ v ++ ": " ++ "-" ++ ".\n" ++ body' ++ ")") <*> body
  pop t f = K $ do
    v <- fresh
    let K body = f (C $ pure v)
    body' <- body
    pure (\body' -> "(κ" ++ v ++ ".\n" ++ body' ++ ")") <*> body

  be (C x) f = C $ do
    v <- fresh
    let C body = f (C $ pure v)
    body' <- body
    pure (\x' body' -> "" ++ x' ++ " be " ++ v ++ ".\n" ++ body' ++ "") <*> x <*> body

  letTo (K x) f = K $ do
    v <- fresh
    let K body = f (C $ pure v)
    body' <- body
    pure (\x' body' -> "" ++ x' ++ " to " ++ v ++ ".\n" ++ body' ++ "") <*> x <*> body

  u64 x = C $ pure (show x)
  constant _ pkg name = K $ pure (pkg ++ "/" ++ name)
  lambdaIntrinsic x = C $ pure (show x)
  cbpvIntrinsic x = C $ pure (show x)

fresh :: State Int String
fresh = do
  n <- get
  put (n + 1)
  pure ("v" ++ show n)
