{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Lambda.AsView (View, view) where

import Control.Category
import Lambda.HasExp
import Lambda
import Lambda.HasProduct
import Lambda.HasSum
import Lambda.HasLet
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

instance HasLet View where
  be (V x) t f = V ("(" ++ x ++ " be " ++ v ++ ": " ++ show t ++ ". " ++ body ++ ")") where
    v = "v?"
    V body = f (V v)

instance Lambda View where
  u64 x = V (show x)
  constant _ pkg name = V $ pkg ++ "/" ++ name
  lambdaConstant _ pkg name = V $ "#" ++ pkg ++ "/" ++ name
