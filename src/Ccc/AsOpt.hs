module Ccc.AsOpt (opt) where

import Ccc
import Ccc.Hom
import Control.Category
import Ccc.AsIntrinsified
import Ccc.AsSimplified
import Prelude hiding ((.), id)

opt :: Closed a b -> Closed a b
opt =
  intrinsify >>>
  (\x -> iterate simplify x !! 20)
