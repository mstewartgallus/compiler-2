{-# LANGUAGE TypeOperators #-}

module Lambda.HasLet (HasLet (..)) where

import Control.Category
import Lambda.Type
import Prelude hiding ((.), id, (<*>), uncurry)

class Category k => HasLet k where
  be :: k x a -> ST a -> (k Unit a -> k x b) -> k x b
