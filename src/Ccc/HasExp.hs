{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Ccc.HasExp (HasExp (..)) where

import Control.Category
import Ccc.HasUnit
import Ccc.Type
import Prelude hiding ((.), id)

class HasUnit k => HasExp k where
  zeta :: ST a -> (k Unit a -> k b c) -> k b (a ~> c)
  pass :: k Unit a -> k (a ~> b) b
