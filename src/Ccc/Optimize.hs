module Ccc.Optimize (optimize) where

import Ccc
import Ccc.Hom
import Control.Category
import Ccc.AsIntrinsified
import Ccc.RemoveDead
import Ccc.ZetaToKappa
import Ccc.Inline
import Ccc.AsLeft
import Ccc.AsRight
import Prelude hiding ((.), id, round)

optimize :: Term hom => hom a b -> Closed a b
optimize =
  intrinsify >>>
  (\x -> iterate round x !! 100)

round :: Term hom => hom a b -> Closed a b
round =
  asRight >>>
  dopass >>>

  asLeft >>>
  dopass

dopass :: Term hom => hom a b -> Closed a b
dopass =
  zetaToKappa >>>
  inline >>>
  removeDead
