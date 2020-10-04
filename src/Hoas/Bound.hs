{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Hoas.Bound (Bound (..)) where

import Hoas.Type
import Prelude hiding ((.), id, (<*>), uncurry)
import Id (Id)
import Data.Word (Word64)
import Control.Category

class Category t => Bound t where
  be :: Id -> t x a -> ST a -> (t Unit a -> t x b) -> t x b

  lam :: Id -> ST a -> (t Unit a -> t x b) -> t x (a ~> b)
  (<*>) :: t x (a ~> b) -> t x a -> t x b

  u64 :: Word64 -> t x U64
  constant :: ST a -> String -> String -> t x a
