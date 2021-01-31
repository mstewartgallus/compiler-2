{-# LANGUAGE DataKinds #-}

module Cbpv.AsOpt (opt) where

import Cbpv
import Cbpv.Hom
import Cbpv.Intrinsify
import Cbpv.MoveCode
import Cbpv.Tuples
import Cbpv.ZetaToPop
import Cbpv.AsLeft
import Cbpv.AsRight
import Cbpv.Inline
import Cbpv.RemoveDead
import Cbpv.ElimThunkForce
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, round)

opt :: Term stack code => code a b -> Closed a b
opt = intrinsify >>>
      (\x -> iterate round x !! 100)

round :: Term stack code => code a b -> Closed a b
round =
  asLeft >>>
  dopass >>>

  asRight >>>
  dopass

dopass :: Term stack code => code a b -> Closed a b
dopass =
  tuples >>>
  moveCode >>>
  zetaToPop >>>
  elimThunkForce >>>
  inline >>>
  removeDead
