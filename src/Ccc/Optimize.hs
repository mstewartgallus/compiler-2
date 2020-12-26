module Ccc.Optimize (optimize) where

import Ccc
import Ccc.Hom
import Control.Category
import Ccc.AsIntrinsified
import Ccc.AsSimplified
import Ccc.AsLeft
import Ccc.AsRight
import Prelude hiding ((.), id, round)

optimize :: Closed a b -> Closed a b
optimize =
  intrinsify >>>
  (\x -> iterate round x !! 100)

round :: Closed a b -> Closed a b
round =
  asRight >>>
  simplify >>>

  asLeft >>>
  simplify
