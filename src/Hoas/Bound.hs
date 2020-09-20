{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Hoas.Bound (Bound (..)) where

import Hoas.Type
import Prelude hiding ((.), id, (<*>), uncurry)
import Id (Id)
import Data.Word (Word64)

class Bound t where
  be :: Id -> t x a -> ST a -> (t Unit a -> t x b) -> t x b

  lam :: Id -> ST a -> (t Unit a -> t x b) -> t x (a ~> b)
  (<*>) :: t x (a ~> b) -> t x a -> t x b

  u64 :: Word64 -> t x U64
  add :: t x (U64 ~> U64 ~> U64)
