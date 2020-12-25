{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}

-- | Remove duplicate force/thunk pairs
module Cbpv.AsOpt (opt) where

import Cbpv
import Cbpv.Hom
import qualified Cbpv.AsRepeat as AsRepeat
import Control.Category
import Cbpv.Sort
import qualified Ccc.Type as Ccc
import qualified Ccc as Ccc
import Prelude hiding ((.), id, fst, snd, Monad (..))

newtype Stk f g a b = K (AsRepeat.Stk f g a b)
newtype Cde f g a b = C (AsRepeat.Cde f g a b)

opt :: Closed @SetTag a b -> Closed @SetTag a b
opt x = Closed $ case abstract x of
  C y -> AsRepeat.repeat 100 y

instance (Category f, Category g) => Category (Stk f g) where
  id = K id
  K f . K g = K (f . g)

instance (Category f, Category g) => Category (Cde f g) where
  id = C id
  C f . C g = C (f . g)

instance Cbpv f g => Code (Cde f g) where
  unit = C unit

  lift (C f) = C (lift f)
  kappa t f = C $ kappa t $ \x -> case f (C x) of
    C y -> y

instance Cbpv f g => Stack (Stk f g) where

instance Cbpv f g => Cbpv (Stk f g) (Cde f g) where
  thunk (K f) = C (thunk f)
  force (C f) = K (force f)

  pass (C f) = K (pass f)
  push (C f) = K (push f)

  zeta t f = K $ zeta t $ \x -> case f (C x) of
    K y -> y
  pop t f = K $ pop t $ \x -> case f (C x) of
    K y -> y

  u64 x = C (u64 x)

  constant t pkg name = K (constant t pkg name)

  cccIntrinsic x = C $ case x of
    Ccc.AddIntrinsic -> addIntrinsic
    _ -> cccIntrinsic x
  cbpvIntrinsic x = C (cbpvIntrinsic x)

-- | fixme.. cleanup this mess
addIntrinsic :: Cbpv stack code => code (U (AsAlgebra (Ccc.U64 Ccc.* Ccc.U64))) (U (AsAlgebra Ccc.U64))
addIntrinsic = thunk (doAdd . force id)

doAdd :: Cbpv stack code => stack (F (U (F U64) * U (F U64))) (F U64)
doAdd =
  pop inferSort $ \tuple ->
  push unit >>>
  force (tuple >>> fst) >>> (pop inferSort $ \x ->
  push unit >>>
  force (tuple >>> snd) >>> (pop inferSort $ \y ->
  push (addi . lift x . y)))

addi :: Cbpv stack code => code (U64 * U64) U64
addi = cbpvIntrinsic AddIntrinsic

fst :: Cbpv stack code => code (a * b) a
fst = kappa undefined (\x -> x . unit)

snd :: Cbpv stack code => code (a * b) b
snd = kappa undefined (\_ -> id)
