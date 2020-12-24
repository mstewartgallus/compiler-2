{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Ccc (Intrinsic (..), Ccc (..)) where

import Ccc.HasExp
import Ccc.HasProduct
import Ccc.Type
import Data.Word (Word64)
import qualified Lam.Type as Lam

-- | A level intermediate language based off cartesian-closed
-- categories and the kappa/zeta calculus decomposition (Hawegawa M.)
-- of the simply typed lambda calculus.
--
-- Hasegawa M. (1995) Decomposing typed lambda calculus into a couple
-- of categorical programming languages.
--
-- In: Pitt D., Rydeheard D.E., Johnstone P. (eds) Category Theory and
-- Computer Science. CTCS 1995. Lecture Notes in Computer Science, vol
-- 953. Springer, Berlin,
-- Heidelberg.
--
-- https://doi.org/10.1007/3-540-60164-3_28
class (HasProduct hom, HasExp hom) => Ccc hom where
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