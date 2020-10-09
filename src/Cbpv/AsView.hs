{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.AsView (Stack, view) where

import Cbpv
import Control.Category
import Control.Monad.State
import Cbpv.Sort
import Prelude hiding ((.), id)

newtype Stack (a :: Algebra) (b :: Algebra) = K (State Int String)

newtype Code (a :: Set) (b :: Set) = C (State Int String)

view :: Code a b -> String
view (C v) = evalState v 0

instance Category Stack where
  id = K $ pure "pass"
  K f . K g = K $ pure (\f' g' -> g' ++ ";\n" ++ f') <*> f <*> g

instance Category Code where
  id = C $ pure "id"
  C f . C g = C $ pure (\f' g' -> f' ++ " ∘ " ++ g') <*> f <*> g

indent = unlines . map ("\t" ++) . lines

instance Cbpv Stack Code where
  return (C f) = K $ pure (\f' -> "return " ++ f' ++ "") <*> f

  thunk (K f) = C $ pure (\f' -> "thunk {" ++ indent ("\n" ++ f')  ++ "}") <*> f
  force (C f) = K $ pure (\f' -> "force " ++ f' ++ "") <*> f

  unit = C $ pure "unit"
  C f &&& C g = C $ pure (\f' g' -> "⟨" ++ f' ++ ", " ++ g' ++ "⟩") <*> f <*> g
  first = C $ pure "π₁"
  second = C $ pure "π₂"

  absurd = C $ pure "absurd"
  C f ||| C g = C $ pure (\f' g' -> "[" ++ f' ++ " , " ++ g' ++ "]") <*> f <*> g
  left = C $ pure "i₁"
  right = C $ pure "i₂"

  pop = K $ pure "pop"
  push = K $ pure "push"

  curry (K f) = K $ pure (\f' -> "λ\n" ++ f' ++ "") <*> f
  uncurry (K f) = K $ pure (\f' -> "!\n" ++ f' ++ "") <*> f

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
