{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}

-- | Run one round of passes
module Cbpv.AsRound (round) where

import Cbpv
import qualified Cbpv.AsSimplified as AsSimplified
import qualified Cbpv.AsLeft as AsLeft
import Control.Category
import Cbpv.Sort
import qualified Cbpv.Hom as Hom
import qualified Ccc.Type as Ccc
import qualified Ccc as Ccc
import Prelude hiding ((.), id, round)

round :: Hom.Closed @SetTag a b -> Hom.Closed a b
round x = AsSimplified.simplify (AsLeft.asLeft x)
