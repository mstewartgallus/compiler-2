{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Convert force (thunk f) to f unit
module Cbpv.ElimThunkForce (elimThunkForce) where

import Cbpv
import Cbpv.Hom
import Cbpv.Sort
import Data.Kind
import Prelude hiding ((.), id, fst, snd)

elimThunkForce :: Closed @SetTag a b -> Closed a b
elimThunkForce x = Closed (out (fold x))

into :: Hom k a b -> Expr k a b
into x = Pure x

out :: Expr k a b -> Hom k a b
out x = case x of
  Pure x -> x
  Thunk f -> thunk (\x -> out (f (into x)))

data Expr (k :: Set -> Set -> Type) (a :: Sort t) (b :: Sort t) where
  Pure :: Hom k a b -> Expr k a b

  Thunk :: (KnownSort a, KnownSort b, KnownSort c) => (Expr k Unit a -> Expr k b c) -> Expr k a (b ~. c)

instance Category (Expr f) where
  id = into id
  f . g = into (out f . out g)

instance Stack (Expr f) where

instance Code (Expr g) where
  unit = into unit

  lift x = into (lift (out x))
  kappa f = into (kappa $ \x -> out (f (into x)))

instance Cbpv (Expr f) (Expr f) where
  thunk = Thunk
  force (Thunk f) = f unit
  force x = into (force (out x))

  push x = into (push (out x))
  pop f = into (pop $ \x -> out (f (into x)))

  pass x = into (pass (out x))
  zeta f = into (zeta $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant pkg name = into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
  cbpvIntrinsic x = into (cbpvIntrinsic x)
