{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Hoas.AsBound (Expr, bindPoints) where

import Id (Stream (..))
import Hoas.Bound
import qualified Hoas
import Hoas.Type
import Control.Category
import Prelude hiding ((.), id, curry, uncurry, (<*>))

newtype Expr t (a :: T) (b :: T) = E (Stream -> t a b)

bindPoints :: Stream -> Expr t a b -> t a b
bindPoints str (E x) = x str

instance Category t => Category (Expr t) where
  id = E $ const id
  E f . E g = E $ \(Stream _ fs gs) -> f fs . g gs

instance Bound t => Hoas.Hoas (Expr t) where
  be (E x) t f = E $ \(Stream n xs ys) -> be n (x xs) t $ \x' -> case f (E $ \_ -> x') of
    E y -> y ys

  lam t f = E $ \(Stream n _ ys) -> lam n t $ \x -> case f (E $ \_ -> x) of
    E y -> y ys
  E f <*> E x = E $ \(Stream _ fs xs) -> f fs <*> x xs

  u64 x = E $ const (u64 x)
  constant t pkg name = E $ const $ constant t pkg name
