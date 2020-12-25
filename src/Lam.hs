{-# LANGUAGE TypeOperators #-}

module Lam (Lam (..), letBe) where

import Data.Word (Word64)
import Lam.Type
import Prelude hiding (id, (.), (<*>))

-- | A simple high level intermediate language based off the simply
-- typed lambda calculus. Evaluation is lazy.
class Lam t where
  lam :: ST a -> (t a -> t b) -> t (a ~> b)
  (<*>) :: t (a ~> b) -> t a -> t b

  be :: t a -> ST a -> (t a -> t b) -> t b

  u64 :: Word64 -> t U64
  constant :: ST a -> String -> String -> t a

  add :: t (U64 ~> U64 ~> U64)
  add = constant inferT "core" "add"

letBe :: (Lam t, KnownT a) => t a -> (t a -> t b) -> t b
letBe x f = be x inferT f
