{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.AsDup (Code, Stack, dup) where

import Cbpv
import Control.Category
import Cbpv.Sort
import Data.Kind
import Prelude hiding ((.), id, Monad (..), uncurry, curry)

data Code
  (f :: Set -> Set -> Type) (g :: Set -> Set -> Type)
  (x :: Algebra -> Algebra -> Type) (y :: Algebra -> Algebra -> Type)
  (a :: Set) (b :: Set) = C (f a b) (g a b)

data Stack
  (f :: Set -> Set -> Type) (g :: Set -> Set -> Type)
  (x :: Algebra -> Algebra -> Type) (y :: Algebra -> Algebra -> Type)
  (a :: Algebra) (b :: Algebra) = K (x a b) (y a b)

dup :: Code f g x y a b -> (f a b, g a b)
dup (C f g) = (f, g)

instance (Category f, Category g) => Category (Code f g x y) where
  id = C id id
  C f f' . C g g' = C (f . g) (f' . g')

instance (Category x, Category y) => Category (Stack f g x y) where
  id = K id id
  K x x' . K y y' = K (x . y) (x' . y')

instance (Cbpv g f, Cbpv g' f') => Cbpv (Stack f f' g g') (Code f f' g g') where
  to (K f f') (K x x') = K (to f x) (to f' x')
  return (C x x') = K (return x) (return x')

  thunk (K x x') = C (thunk x) (thunk x')
  force (C f f') = K (force f) (force f')

  unit = C unit unit
  C f f' &&& C g g' = C (f &&& g) (f' &&& g')
  first = C first first
  second = C second second

  absurd = C absurd absurd
  C f f' ||| C g g' = C (f ||| g) (f' ||| g')
  left = C left left
  right = C right right

  assocOut = K assocOut assocOut
  assocIn = K assocIn assocIn

  curry (K f f') = K (curry f) (curry f')
  uncurry (K f f') = K (uncurry f) (uncurry f')

  u64 x = C (u64 x) (u64 x)
  add = C add add
  addLazy = K addLazy addLazy
