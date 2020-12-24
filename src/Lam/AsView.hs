{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Lam.AsView (View, view) where

import Lam hiding ((<*>))
import qualified Lam as H ((<*>))
import Lam.Type
import Control.Category
import Control.Monad.State

newtype View (a :: T) = V (State Int String)

view :: View a -> String
view (V v) = evalState v 0

instance Lam View where
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
