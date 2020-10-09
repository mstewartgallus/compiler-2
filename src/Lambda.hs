{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

-- |
--
-- Export the final type class of the simple lambda calculus language.
-- Here we finish the Lambda type class off with some basic operations on
-- integers.
module Lambda (Intrinsic (..), Lambda (..)) where

import Data.Word (Word64)
import qualified Hoas.Type as Hoas
import Lambda.HasExp
import Lambda.HasLet
import Lambda.HasProduct
import Lambda.HasSum
import Lambda.Type

class (HasSum hom, HasProduct hom, HasExp hom, HasLet hom) => Lambda hom where
  u64 :: Word64 -> hom Unit U64
  constant :: Hoas.ST a -> String -> String -> hom Unit (AsObject a)
  lambdaIntrinsic :: Intrinsic a b -> hom a b

  add :: hom (U64 * U64) U64
  add = lambdaIntrinsic AddIntrinsic

data Intrinsic a b where
  AddIntrinsic :: Intrinsic (U64 * U64) U64

instance Show (Intrinsic a b) where
  show x = case x of
    AddIntrinsic -> "#add"
