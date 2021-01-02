{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Ccc (Intrinsic (..), Ccc (..)) where

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
class Ccc hom where
  id :: KnownT a => hom a a
  (.) :: (KnownT a, KnownT b, KnownT c) => hom b c -> hom a b -> hom a c

  unit :: KnownT a => hom a Unit

  zeta :: (KnownT a, KnownT b, KnownT c) => (hom Unit a -> hom b c) -> hom b (a ~> c)
  pass :: (KnownT a, KnownT b) => hom Unit a -> hom (a ~> b) b

  kappa :: (KnownT a, KnownT b, KnownT c) => (hom Unit a -> hom b c) -> hom (a * b) c
  lift :: (KnownT a, KnownT b) => hom Unit a -> hom b (a * b)

  u64 :: Word64 -> hom Unit U64
  constant :: Lam.KnownT a => String -> String -> hom Unit (AsObject a)
  cccIntrinsic :: (KnownT a, KnownT b) => Intrinsic a b -> hom a b

data Intrinsic a b where
  AddIntrinsic :: Intrinsic (U64 * U64) U64
  MulIntrinsic :: Intrinsic (U64 * U64) U64

instance Show (Intrinsic a b) where
  show x = case x of
    AddIntrinsic -> "#add"
    MulIntrinsic -> "#mul"
