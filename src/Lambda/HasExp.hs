{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Lambda.HasExp (HasExp (..)) where

import Control.Category
import Lambda.HasUnit
import Lambda.Type
import Prelude hiding ((.), id)

class HasUnit k => HasExp k where
  zeta :: ST a -> (k Unit a -> k b c) -> k b (a ~> c)
  pass :: k Unit a -> k (a ~> b) b
