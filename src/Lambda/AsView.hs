{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Lambda.AsView (View, view) where

import Control.Category
import Lambda.HasExp hiding ((<*>))
import Lambda
import Lambda.HasProduct
import Lambda.HasSum
import Lambda.HasLet
import Lambda.Type
import Control.Monad.State

newtype View (a :: T) (b :: T) = V (State Int String)

view :: View a b -> String
view (V v) = evalState v 0

instance Category View where
  id = V $ pure "id"
  V f . V g = V $ pure (\f' g' -> f' ++ " ∘ " ++ g') <*> f <*> g

instance HasProduct View where
  unit = V $ pure "unit"

  V f &&& V g = V $ pure (\f' g' -> "⟨" ++ f' ++ " , " ++ g' ++ "⟩") <*> f <*> g
  first = V $ pure "π₁"
  second = V $ pure "π₂"

instance HasSum View where
  absurd = V $ pure "absurd"

  V f ||| V g = V $ pure (\f' g' -> "[" ++ f' ++ " , " ++ g' ++ "]") <*> f <*> g
  left = V $ pure "i₁"
  right = V $ pure "i₂"

instance HasExp View where
  curry (V f) = V $ pure (\f' -> "(λ " ++ f' ++ ")") <*> f
  uncurry (V f) = V $ pure (\f' -> "(! " ++ f' ++ ")") <*> f

instance HasLet View where
  be t (V x) f = V $ do
    v <- fresh
    let V body = f (V $ pure v)
    pure (\x' body' -> "(" ++ x' ++ " be " ++ v ++ ": " ++ show t ++ ".\n" ++ body' ++ ")") <*> x <*> body

instance Lambda View where
  u64 x = V $ pure (show x)
  constant _ pkg name = V $ pure (pkg ++ "/" ++ name)
  lambdaConstant _ pkg name = V $ pure ("#" ++ pkg ++ "/" ++ name)

fresh :: State Int String
fresh = do
  n <- get
  put (n + 1)
  pure ("v" ++ show n)
