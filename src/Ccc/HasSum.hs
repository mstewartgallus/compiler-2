{-# LANGUAGE TypeOperators #-}

module Ccc.HasSum (HasSum (..)) where

import Control.Category
import Ccc.Type

class Category k => HasSum k where
  absurd :: k Void x

  (|||) :: k a c -> k b c -> k (a + b) c
  left :: k a (a + b)
  right :: k b (a + b)

infixl 9 |||
