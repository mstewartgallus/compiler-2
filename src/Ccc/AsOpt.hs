module Ccc.AsOpt (optimize) where

import Ccc
import Ccc.Hom
import Control.Category
import Ccc.AsIntrinsified
import Ccc.AsSimplified
import Prelude hiding ((.), id, round)

optimize :: Closed a b -> Closed a b
optimize =
  intrinsify >>>
  (\x -> iterate round x !! 20)

round :: Closed a b -> Closed a b
round =
  simplify
