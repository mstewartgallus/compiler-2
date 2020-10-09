{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Lambda.HasLet (HasLet (..)) where

import Control.Category
import Lambda.Type
import Lambda.HasProduct
import Prelude hiding ((.), id, (<*>), uncurry)

class HasProduct k => HasLet k where
  be :: ST a -> (k Unit a -> k x b) -> k (a * x) b
