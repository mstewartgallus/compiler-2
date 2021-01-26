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

elimThunkForce :: Closed @Set a b -> Closed a b
elimThunkForce x = Closed (out (fold x))

into :: Hom k a b -> Expr k a b
into x = Pure x

out :: Expr k a b -> Hom k a b
out x = case x of
  Pure x -> x
  Thunk f -> thunk (\x -> out (f (into x)))

data Expr (k :: Set -> Set -> Type) (a :: t) (b :: t) where
  Pure :: Hom k a b -> Expr k a b

  Thunk :: (KnownSet a, KnownAlgebra b, KnownAlgebra c) => (Expr k Unit a -> Expr k b c) -> Expr k a (b ~. c)

instance Stack (Expr f) where
  skip = into skip
  f <<< g = into (out f <<< out g)

instance Code (Expr g) where
  id = into id
  f . g = into (out f . out g)

  unit = into unit
  fst = into fst
  snd = into snd
  x &&& y = into (out x &&& out y)

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
