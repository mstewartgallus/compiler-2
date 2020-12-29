{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Intrinsify intrinsics
module Cbpv.AsIntrinsified (intrinsify) where

import Cbpv
import Control.Category
import qualified Cbpv.Hom as Hom
import Cbpv.Sort
import Data.Kind
import Prelude hiding ((.), id, fst, snd)
import qualified Ccc.Type as Ccc
import qualified Ccc as Ccc

intrinsify :: Hom.Closed @SetTag a b -> Hom.Closed a b
intrinsify x = Hom.Closed (outC (Hom.fold x))

newtype Stk f (g :: Set -> Set -> Type) (a :: Algebra) (b :: Algebra) = K (f a b)
newtype Cde (f :: Algebra -> Algebra -> Type) g (a :: Set) (b :: Set) = C { outC :: g a b }

instance (Category f, Category g) => Category (Stk f g) where
  id = K id
  K f . K g = K (f . g)

instance (Category f, Category g) => Category (Cde f g) where
  id = C id
  C f . C g = C (f . g)

instance Cbpv f g => Code (Cde f g) where
  unit = C unit
  fst = C fst
  snd = C snd
  C x &&& C y = C (x &&& y)

instance Cbpv f g => Stack (Stk f g) where

instance Cbpv f g => Cbpv (Stk f g) (Cde f g) where
  thunk (K f) = C (thunk f)
  force (C f) = K (force f)

  pass (C x) = K (pass x)
  lift (C x) = K (lift x)

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
  (force (fst . tuple) >>>
   (pop inferSort $ \x ->
   (force (snd . tuple) >>>
   (pop inferSort $ \y ->
   lift (addi . (x &&& y)))) . lift unit)) . lift unit

addi :: Cbpv stack code => code (U64 * U64) U64
addi = cbpvIntrinsic AddIntrinsic
