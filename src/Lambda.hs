{-# LANGUAGE TypeOperators #-}

-- |
--
-- Export the final type class of the simple lambda calculus language.
-- Here we finish the Lambda type class off with some basic operations on
-- integers.
module Lambda (Lambda (..)) where

import Data.Word (Word64)
import Lambda.HasExp
import Lambda.HasProduct
import Lambda.HasSum
import Lambda.Type

class (HasSum hom, HasProduct hom, HasExp hom) => Lambda hom where
  u64 :: Word64 -> hom Unit U64
  constant :: ST a -> String -> String -> hom Unit a
