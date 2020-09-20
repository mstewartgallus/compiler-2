{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Term.AsView (View, view) where

import Term
import Hoas.Type

newtype View (env :: [T]) (a :: T) = V String

view :: View env a -> String
view (V v) = v

instance Term View where
  unit = V "unit"
  V x `be` V f = V ("(" ++ x ++ " be " ++ f ++ ")")
  V f <*> V x = V ("(" ++ f ++ " " ++ x ++ ")")

  u64 n = V (show n)
  add = V "add"

  tip = V "I"
  const (V x) = V ("(K " ++ x ++ ")")

  curry (V f) = V ("(λ " ++ f ++ ")")
