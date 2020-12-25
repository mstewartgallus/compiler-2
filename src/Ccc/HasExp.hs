{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Ccc.HasExp (HasExp (..)) where

import Control.Category
import Ccc.HasUnit
import Ccc.Type
import Prelude hiding ((.), id, (<*>))

-- | Our intermediate language is based off of the usual formulation
-- of cartesian-closed categories but we use a higher order abstract
-- syntax based approach because juggling the stack with combinators
-- is really awkward.
class HasUnit k => HasExp k where
  zeta :: ST a -> (k Unit a -> k b c) -> k b (a ~> c)
  app :: k b (a ~> c) -> k Unit a -> k b c

  -- | fixme.. deprecate..
  pass :: k Unit a -> k (a ~> b) b
  pass = app id
