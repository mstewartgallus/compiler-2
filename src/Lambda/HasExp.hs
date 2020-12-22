{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Lambda.HasExp (HasExp (..)) where

import Control.Category
import Lambda.HasProduct
import Lambda.Type
import Prelude hiding ((.), id, (<*>), uncurry)

-- | The categorical definition of an exponential (function type.)
class HasProduct k => HasExp k where
  zeta :: ST a -> (k Unit a -> k b c) -> k b (a ~> c)
  pass :: k Unit a -> k (a ~> b) b
