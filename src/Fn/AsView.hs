{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Fn.AsView (View, view) where

import Fn
import Term.Type

newtype View (env :: [T]) (a :: T) = View String

view :: View env a -> String
view (View v) = v

instance Fn View where
  View x `be` View f = View ("(" ++ x ++ " be " ++ f ++ ")")
  View f <*> View x = View ("(" ++ f ++ " " ++ x ++ ")")

  u64 n = View (show n)
  add = View "add"

  head = View "I"
  tail (View x) = View ("(S " ++ x ++ ")")

  curry (View f) = View ("(λ " ++ f ++ ")")
