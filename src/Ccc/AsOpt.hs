{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Ccc.AsOpt (opt) where

import Ccc
import Ccc.Hom
import Control.Category
import Ccc.HasExp
import Ccc.HasUnit
import Ccc.HasProduct
import Ccc.Type
import qualified Lam.Type as Lam
import qualified Ccc.AsRepeat as AsRepeat
import qualified Ccc.AsIntrinsified as AsIntrinsified
import Prelude hiding ((.), id, curry, uncurry, Monad (..), Either (..))

opt :: Closed a b -> Closed a b
opt =
  AsIntrinsified.intrinsify >>>
  AsRepeat.repeat 20
