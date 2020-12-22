{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Lambda.HasProduct (HasProduct (..)) where

import Control.Category
import Lambda.Type

class Category k => HasProduct k where
  unit :: k x Unit

  kappa :: ST a -> (k Unit a -> k b c) -> k (a * b) c
  lift :: k Unit a -> k b (a * b)
