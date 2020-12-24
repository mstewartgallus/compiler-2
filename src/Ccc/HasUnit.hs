module Ccc.HasUnit (HasUnit (..)) where

import Control.Category
import Ccc.Type

class Category k => HasUnit k where
  unit :: k x Unit
