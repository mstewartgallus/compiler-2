{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Ccc.HasProduct (HasProduct (..)) where

import Control.Category
import Ccc.Type
import Ccc.HasUnit

class HasUnit k => HasProduct k where
  kappa :: ST a -> (k Unit a -> k b c) -> k (a * b) c
  lift :: k Unit a -> k b (a * b)
