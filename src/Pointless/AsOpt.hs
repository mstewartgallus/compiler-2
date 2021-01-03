{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Pointless.AsOpt (opt) where

import Pointless
import Pointless.Hom
import Pointless.AsLeft
import Pointless.Tuples
import Pointless.AsRight
import Pointless.RemoveDead
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, round)

opt :: Hom @SetTag a b -> Hom @SetTag a b
opt = (\x -> iterate round x !! 100)

round :: Hom @SetTag a b -> Hom @SetTag a b
round =
  asLeft >>>
  dopass >>>

  asRight >>>
  dopass

dopass :: Hom @SetTag a b -> Hom @SetTag a b
dopass =
  tuples >>>
  removeDead
