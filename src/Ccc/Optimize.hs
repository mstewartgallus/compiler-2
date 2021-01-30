module Ccc.Optimize (optimize) where

import Ccc
import Control.Category
import Ccc.AsIntrinsified
import Ccc.RemoveDead
import Ccc.ZetaToKappa
import Ccc.Inline
import Ccc.AsLeft
import Ccc.AsRight
import Prelude hiding ((.), id, round)

optimize :: Term hom => hom a b -> RemoveDead a b
optimize =
  intrinsify >>>
  dorounds 100

dorounds :: Term hom => Int -> hom a b -> RemoveDead a b
dorounds n x | n == 0 = round x
             | otherwise = dorounds (n - 1) (round x)

round :: Term hom => hom a b -> RemoveDead a b
round =
  asRight >>>
  dopass >>>

  asLeft >>>
  dopass

dopass :: Term hom => hom a b -> RemoveDead a b
dopass =
  zetaToKappa >>>
  inline >>>
  removeDead
