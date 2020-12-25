{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Ccc.HasProduct (HasProduct (..)) where

import Control.Category
import Ccc.Type
import Ccc.HasUnit
import Prelude hiding (id)

class HasUnit k => HasProduct k where
  kappa :: ST a -> (k Unit a -> k b c) -> k (a * b) c
  whereIs :: k (a * b) c -> k Unit a -> k b c

  -- | fixme... deprecate ?
  lift :: k Unit a -> k b (a * b)
  lift = whereIs id
