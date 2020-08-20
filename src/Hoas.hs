{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Hoas (Hoas (..)) where

import Product
import Sum
import Type

class (Sum k, Product k) => Hoas k where
  var :: ST a -> (Value k a -> k env b) -> k (env * a) b
  label :: ST a -> (Continuation k a -> k b env) -> k b (env + a)
