{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Hoas (Hoas (..), letBe) where

import Control.Category
import Data.Word (Word64)
import Hoas.Type
import Prelude hiding (id, uncurry, (.), (<*>))

class Hoas t where
  be :: t a -> ST a -> (t a -> t b) -> t b

  lam :: ST a -> (t a -> t b) -> t (a ~> b)
  (<*>) :: t (a ~> b) -> t a -> t b

  u64 :: Word64 -> t U64
  add :: t (U64 ~> U64 ~> U64)
  add = constant inferT "core" "add"

  constant :: ST a -> String -> String -> t a

letBe :: (KnownT a, Hoas t) => t a -> (t a -> t b) -> t b
letBe x f = be x inferT f
