{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

-- |
--
-- Export the final type class of the simple ccc calculus language.
-- Here we finish the Ccc type class off with some basic operations on
-- integers.
module Ccc (Intrinsic (..), Ccc (..)) where

import Ccc.HasExp
import Ccc.HasProduct
import Ccc.HasSum
import Ccc.Type
import Data.Word (Word64)
import qualified Lam.Type as Lam

class (HasSum hom, HasProduct hom, HasExp hom) => Ccc hom where
  u64 :: Word64 -> hom Unit U64
  constant :: Lam.ST a -> String -> String -> hom Unit (AsObject a)
  cccIntrinsic :: Intrinsic a b -> hom a b

  add :: hom (U64 * U64) U64
  add = cccIntrinsic AddIntrinsic

data Intrinsic a b where
  AddIntrinsic :: Intrinsic (U64 * U64) U64

instance Show (Intrinsic a b) where
  show x = case x of
    AddIntrinsic -> "#add"
