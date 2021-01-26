{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Cbpv.AsOpt (opt) where

import Cbpv
import Cbpv.Hom
import Cbpv.Intrinsify
import Cbpv.MoveCode
import Cbpv.Tuples
import Cbpv.ZetaToPop
import Cbpv.Inline
import Cbpv.RemoveDead
import Cbpv.ElimThunkForce
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, round)

opt :: Closed @Set a b -> Closed @Set a b
opt = intrinsify >>>
      (\x -> iterate round x !! 100)

round :: Closed @Set a b -> Closed @Set a b
round =
  -- fixme.. implement left/right again
  dopass

dopass :: Closed @Set a b -> Closed @Set a b
dopass =
  tuples >>>
  moveCode >>>
  zetaToPop >>>
  elimThunkForce >>>
  inline >>>
  removeDead
