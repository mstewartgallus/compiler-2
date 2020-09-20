{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Hoas (Hoas (..), letBe) where

import Data.Word (Word64)
import Hoas.Type
import Prelude hiding (id, uncurry, (.), (<*>))

class Hoas t where
  lam :: ST a -> (t Unit a -> t x b) -> t x (a ~> b)
  (<*>) :: t x (a ~> b) -> t x a -> t x b

  u64 :: Word64 -> t x U64
  add :: t x (U64 ~> U64 ~> U64)

  be :: t x a -> ST a -> (t Unit a -> t x b) -> t x b
  be x t f = lam t f <*> x

letBe :: (KnownT a, Hoas t) => t x a -> (t Unit a -> t x b) -> t x b
letBe x f = be x inferT f
