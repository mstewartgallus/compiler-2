{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.Intrinsify (intrinsify) where

import Cbpv
import qualified Ccc
import qualified Ccc.Type as Ccc
import Cbpv.Hom
import Cbpv.Sort
import Data.Kind
import Prelude hiding ((.), id, fst, snd)

intrinsify :: Closed @SetTag a b -> Closed a b
intrinsify x = Closed (out (fold x))

binop :: Cbpv stack code => Intrinsic (U64 * U64) U64 -> stack (AsAlgebra (Ccc.U64 Ccc.* Ccc.U64)) (AsAlgebra Ccc.U64)
binop intrins =
  pop $ \tuple -> (
  (pop $ \x -> (
  (pop $ \y ->
  push (cbpvIntrinsic intrins . lift x . y)) .
  force (snd . tuple))) .
  force (fst . tuple))

into :: Hom k a b -> Expr k a b
into = Pure

out :: Expr k a b -> Hom k a b
out (Pure x) = x

newtype Expr (k :: Set -> Set -> Type) (a :: Sort t) (b :: Sort t) = Pure (Hom k a b)

instance Category (Expr f) where
  id = into id
  f . g = into (out f . out g)

instance Stack (Expr f) where

instance Code (Expr g) where
  unit = into unit

  lift x = into (lift (out x))
  kappa f = into (kappa $ \x -> out (f (into x)))

instance Cbpv (Expr f) (Expr f) where
  cccIntrinsic Ccc.AddIntrinsic = binop AddIntrinsic
  cccIntrinsic Ccc.MulIntrinsic = binop MulIntrinsic

  thunk f = into (thunk $ \x -> out (f (into x)))
  force x = into (force (out x))

  push x = into (push (out x))
  pop f = into (pop $ \x -> out (f (into x)))

  pass x = into (pass (out x))
  zeta f = into (zeta $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant pkg name = into (constant pkg name)
  cbpvIntrinsic x = into (cbpvIntrinsic x)
