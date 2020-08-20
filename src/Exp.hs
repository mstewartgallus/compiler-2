{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Exp (Exp (..)) where

import Control.Category
import Data.Kind (Type)
import Product
import Type
import Prelude hiding ((.), id)

class Product k => Exp k where
  lambda :: k (env * a) b -> k env (a ~> b)
  unlambda :: k env (a ~> b) -> k (env * a) b

  eval :: k ((a ~> b) * a) b
  eval = unlambda id

  (<*>) :: k env (a ~> b) -> k env a -> k env b
  f <*> x = eval <<< (f # x)
