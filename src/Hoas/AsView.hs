{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Hoas.AsView (View, view) where

import Hoas hiding ((<*>))
import qualified Hoas as H ((<*>))
import Hoas.Type
import Control.Category
import Control.Monad.State

newtype View (a :: T) (b :: T) = V (State Int String)

view :: View a b -> String
view (V v) = evalState v 0

instance Category View where
  id = V $ pure "id"
  V f . V g = V $ pure (\f' g' -> f' ++ " . " ++ g') <*> f <*> g

instance Hoas View where
  be (V x) t f = V $ do
    v <- fresh
    let V body = f (V $ pure v)
    pure (\x' body' -> x' ++ " be " ++ v ++ ": " ++ show t ++ ".\n" ++ body') <*> x <*> body

  lam t f = V $ do
    v <- fresh
    let V body = f (V $ pure v)
    pure (\body' -> "λ " ++ v ++ ": " ++ show t ++ ".\n" ++ body') <*> body

  V f <*> V x = V $ pure (\f' x' -> "(" ++ f' ++ " " ++ x' ++ ")") <*> f <*> x

  u64 n = V $ pure (show n)
  constant _ pkg name = V $ pure (pkg ++ "/" ++ name)

fresh :: State Int String
fresh = do
  n <- get
  put (n + 1)
  pure ("v" ++ show n)
