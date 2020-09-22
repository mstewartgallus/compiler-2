{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.AsView (Stack, view) where

import Cbpv
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id)

newtype Stack (a :: Algebra) (b :: Algebra) = K String

newtype Code (a :: Set) (b :: Set) = C String

view :: Code a b -> String
view (C v) = v

instance Category Stack where
  id = K "id"
  K f . K g = K (f ++ " ∘ " ++ g)

instance Category Code where
  id = C "id"
  C f . C g = C (f ++ " ∘ " ++ g)

instance Cbpv Stack Code where
  to (K f) (K x) = K ("(to " ++ f ++ " " ++ x ++ ")")
  return (C f) = K ("(return " ++ f ++ ")")

  thunk (K f) = C ("(thunk " ++ f ++ ")")
  force (C f) = K ("(force " ++ f ++ ")")

  unit = C "unit"
  C f &&& C x = C ("⟨" ++ f ++ " , " ++ x ++ "⟩")
  first = C "π₁"
  second = C "π₂"

  absurd = C "absurd"
  C f ||| C x = C ("[" ++ f ++ " , " ++ x ++ "]")
  left = C "i₁"
  right = C "i₂"

  assocOut = K "out"
  assocIn = K "in"

  curry (K f) = K ("(λ " ++ f ++ ")")
  uncurry (K f) = K ("(! " ++ f ++ ")")

  u64 x = C (show x)
  add = C "add"
  addLazy = K "add"
