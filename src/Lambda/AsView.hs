{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module Lambda.AsView (View, view) where

import Control.Category
import Lambda.HasExp hiding ((<*>))
import Lambda
import Lambda.HasUnit
import Lambda.HasProduct
import Lambda.HasSum
import Lambda.Type
import Control.Monad.State

newtype View (a :: T) (b :: T) = V (State Int String)

view :: View a b -> String
view (V v) = evalState v 0

instance Category View where
  id = V $ pure "id"
  V f . V g = V $ pure (\f' g' -> "(" ++ f' ++ " ∘ " ++ g' ++ ")") <*> f <*> g

instance HasUnit View where
  unit = V $ pure "unit"

instance HasProduct View where
  lift (V f) = V $ pure (\f' -> "(lift " ++ f' ++ ")") <*> f
  kappa t f =  V $ do
    v <- fresh
    let V body = f (V $ pure v)
    pure (\body' -> "(κ " ++ v ++ ": " ++ show t ++ ". " ++ body' ++ ")") <*> body

instance HasExp View where
  pass (V x) = V $ pure (\x' -> "(pass " ++ x') <*> x
  zeta t f = V $ do
    v <- fresh
    let V body = f (V $ pure v)
    pure (\body' -> "(ζ " ++ v ++ ": " ++ show t ++ ". " ++ body' ++ ")") <*> body

instance HasSum View where
  absurd = V $ pure "absurd"

  V f ||| V g = V $ pure (\f' g' -> "[" ++ f' ++ " , " ++ g' ++ "]") <*> f <*> g
  left = V $ pure "i₁"
  right = V $ pure "i₂"

instance Lambda View where
  u64 x = V $ pure (show x)
  constant _ pkg name = V $ pure (pkg ++ "/" ++ name)
  lambdaIntrinsic x = V $ pure (show x)

fresh :: State Int String
fresh = do
  n <- get
  put (n + 1)
  pure ("v" ++ show n)
