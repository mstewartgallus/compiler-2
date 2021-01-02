{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Cbpv.AsOpt (opt) where

import Cbpv
import Cbpv.Hom
import Cbpv.AsIntrinsified
import Cbpv.AsSimplified
import Cbpv.AsLeft
import Cbpv.AsRight
import Cbpv.RemoveDead
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, round)

opt :: Closed @SetTag a b -> Closed @SetTag a b
opt = intrinsify >>>
      (\x -> iterate round x !! 100)

round :: Closed @SetTag a b -> Closed @SetTag a b
round =
  asRight >>>
  dopass >>>

  asLeft >>>
  dopass

dopass :: Closed @SetTag a b -> Closed @SetTag a b
dopass =
  simplify >>>
  removeDead
