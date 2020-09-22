{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Lambda.AsView (View, view) where

import Control.Category
import Lambda.HasExp
import Lambda
import Lambda.HasProduct
import Lambda.HasSum
import Lambda.Type

newtype View (a :: T) (b :: T) = V String

view :: View a b -> String
view (V v) = v

instance Category View where
  id = V "id"
  V f . V g = V (f ++ " ∘ " ++ g)

instance HasProduct View where
  unit = V "unit"

  V f &&& V x = V ("⟨" ++ f ++ " , " ++ x ++ "⟩")
  first = V "π₁"
  second = V "π₂"

instance HasSum View where
  absurd = V "absurd"

  V f ||| V x = V ("[" ++ f ++ " , " ++ x ++ "]")
  left = V "i₁"
  right = V "i₂"

instance HasExp View where
  curry (V f) = V ("(λ " ++ f ++ ")")
  uncurry (V f) = V ("(! " ++ f ++ ")")

instance Lambda View where
  u64 x = V (show x)
  add = V "add"
