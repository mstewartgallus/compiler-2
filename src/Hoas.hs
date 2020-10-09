{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Hoas (Hoas (..), letBe) where

import Control.Category
import Data.Word (Word64)
import Hoas.Type
import Prelude hiding (id, uncurry, (.), (<*>))

class Category t => Hoas t where
  lam :: ST a -> (t Unit a -> t x b) -> t x (a ~> b)
  (<*>) :: t x (a ~> b) -> t x a -> t x b

  be :: t x a -> ST a -> (t Unit a -> t x b) -> t x b

  u64 :: Word64 -> t Unit U64
  add :: t Unit (U64 ~> U64 ~> U64)
  add = constant inferT "core" "add"

  constant :: ST a -> String -> String -> t Unit a

letBe :: (KnownT a, Hoas t) => t x a -> (t Unit a -> t x b) -> t x b
letBe x f = be x inferT f
