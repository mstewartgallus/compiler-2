{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Lambda.HasLet (HasLet (..)) where

import Control.Category
import Lambda.Type
import Prelude hiding ((.), id, (<*>), uncurry)

class Category t => HasLet t where
  be :: ST a -> t x a -> (t Unit a -> t x b) -> t x b
