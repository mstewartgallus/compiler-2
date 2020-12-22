{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

-- | Remove duplicate force/thunk pairs
module Cbpv.AsOpt (Stk, Cde, opt) where

import Cbpv
import qualified Cbpv.AsRepeat as AsRepeat
import Control.Category
import Cbpv.Sort
import qualified Lambda.Type as Lambda
import qualified Lambda as Lambda
import Prelude hiding ((.), id, curry, uncurry, Monad (..))

newtype Stk f g a b = K (AsRepeat.Stk f g a b)
newtype Cde f g a b = C (AsRepeat.Cde f g a b)

opt :: Cde f g a b -> g a b
opt (C x) = AsRepeat.repeat 100 x

instance (Category f, Category g) => Category (Stk f g) where
  id = K id
  K f . K g = K (f . g)

instance (Category f, Category g) => Category (Cde f g) where
  id = C id
  C f . C g = C (f . g)

instance Cbpv f g => Code (Cde f g) where
  unit = C unit

  absurd = C absurd
  C f ||| C g = C (f ||| g)
  left = C left
  right = C right

  lift (C f) = C (lift f)
  kappa t f = C $ kappa t $ \x -> case f (C x) of
    C y -> y

instance Cbpv f g => Stack (Stk f g) where

instance Cbpv f g => Cbpv (Stk f g) (Cde f g) where
  thunk (K f) = C (thunk f)
  force (C f) = K (force f)

  return (C f) = K (return f)
  pass (C f) = K (pass f)
  push (C f) = K (push f)

  be (C x) f = C $ be x $ \x' -> case f (C x') of
    C y -> y

  letTo (K x) f = K $ letTo x $ \x' -> case f (C x') of
    K y -> y

  zeta t f = K $ zeta t $ \x -> case f (C x) of
    K y -> y
  pop t f = K $ pop t $ \x -> case f (C x) of
    K y -> y

  u64 x = C (u64 x)

  constant t pkg name = K (constant t pkg name)

  lambdaIntrinsic x = C $ case x of
    Lambda.AddIntrinsic -> addIntrinsic
    _ -> lambdaIntrinsic x
  cbpvIntrinsic x = C (cbpvIntrinsic x)

-- | fixme.. cleanup this mess
addIntrinsic :: Cbpv stack code => code (U (AsAlgebra (Lambda.U64 Lambda.* Lambda.U64))) (U (AsAlgebra Lambda.U64))
addIntrinsic = thunk (doAdd . force id)

doAdd :: Cbpv stack code => stack (U (F U64) & F (U (F U64))) (F U64)
doAdd =
  pop inferSet $ \x ->
  pop inferSet $ \y ->
  push unit >>>
  force x >>> (
  pop inferSet $ \x' ->
  push unit >>>
  force y >>> (
  pop inferSet $ \y' ->
  push (addi . lift x' . y')))

addi :: Cbpv stack code => code (U64 * U64) U64
addi = cbpvIntrinsic AddIntrinsic
