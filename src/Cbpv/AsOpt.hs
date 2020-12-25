{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}

module Cbpv.AsOpt (opt) where

import Cbpv
import Cbpv.Hom
import qualified Cbpv.AsRepeat as AsRepeat
import qualified Cbpv.AsIntrinsified as AsIntrinsified
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, fst, snd, Monad (..))

opt :: Closed @SetTag a b -> Closed @SetTag a b
opt = AsIntrinsified.intrinsify >>>
      AsRepeat.repeat 100
