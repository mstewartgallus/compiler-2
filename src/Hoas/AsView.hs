{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Hoas.AsView (View, view) where

import Hoas.Bound
import Hoas.Type
import Control.Category

newtype View (a :: T) (b :: T) = V String

view :: View a b -> String
view (V v) = v

instance Category View where
  id = V "id"
  V f . V g = V $ f ++ " . " ++ g

instance Bound View where
  be n (V x) t f = V (x ++ " be " ++ v ++ ": " ++ show t ++ ".\n" ++ body) where
        v = "v" ++ show n
        V body = f (V v)

  lam n t f = V ("λ " ++ v ++ ": " ++ show t ++ ".\n" ++ body) where
        v = "v" ++ show n
        V body = f (V v)

  V f <*> V x = V ("(" ++ f ++ " " ++ x ++ ")")

  u64 n = V (show n)
  add = V "add"
