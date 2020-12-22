module Lambda.HasUnit (HasUnit (..)) where

import Control.Category
import Lambda.Type

class Category k => HasUnit k where
  unit :: k x Unit
