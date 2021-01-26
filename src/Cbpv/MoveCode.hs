{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Move Code
module Cbpv.MoveCode (moveCode) where

import Cbpv
import Cbpv.Hom
import Cbpv.Sort
import Data.Kind
import Prelude hiding ((.), id, fst, snd)

moveCode :: Closed @Set a b -> Closed a b
moveCode x = Closed (out (fold x))

into :: Hom k a b -> Expr k a b
into x = Pure x

out :: Expr k a b -> Hom k a b
out x = case x of
  Pure x -> x

  Thunk f -> thunk (\x -> out (f (into x)))
  Pop f -> pop (\x -> out (f (into x)))
  Zeta f -> zeta (\x -> out (f (into x)))

data Expr (k :: Set -> Set -> Type) (a :: t) (b :: t) where
  Pure :: Hom k a b -> Expr k a b

  Zeta :: (KnownSet a, KnownAlgebra b, KnownAlgebra c) => (Expr f Unit a -> Expr f b c) -> Expr f b (a ~> c)
  Pop :: (KnownSet a, KnownAlgebra b, KnownAlgebra c) => (Expr f Unit a -> Expr f b c) -> Expr f (a & b) c
  Thunk :: (KnownSet a, KnownAlgebra b, KnownAlgebra c) => (Expr k Unit a -> Expr k b c) -> Expr k a (b ~. c)


instance Stack (Expr f) where
  skip = into skip

  y <<< Pop f = pop (\x -> y <<< f x)
  Zeta f <<< y = zeta (\x -> f x <<< y)
  f <<< g = into (out f <<< out g)

instance Code (Expr g) where
  id = into id

  Thunk f . y = thunk (\x -> f (y . x))
  f . g = into (out f . out g)

  unit = into unit
  fst = into fst
  snd = into snd
  x &&& y = into (out x &&& out y)

instance Cbpv (Expr f) (Expr f) where
  thunk = Thunk
  pop = Pop
  zeta = Zeta

  force x = into (force (out x))
  push x = into (push (out x))
  pass x = into (pass (out x))

  u64 n = into (u64 n)
  constant pkg name = into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
  cbpvIntrinsic x = into (cbpvIntrinsic x)
