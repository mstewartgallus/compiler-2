{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

module Cbpv.AsRepeat (repeat) where

import Cbpv
import qualified Cbpv.AsRound as AsRound
import Control.Category
import Cbpv.Sort
import qualified Cbpv.Hom as Hom
import Prelude hiding ((.), id, repeat)

repeat :: Int -> Hom.Closed @SetTag a b -> Hom.Closed a b
repeat = loop

loop :: Int -> Hom.Closed @SetTag a b -> Hom.Closed a b
loop n x | n == 0 = x
         | otherwise = loop (n - 1) (AsRound.round x)
