{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Inline pop f . push x to f x (always so far)
module Cbpv.Inline (inline) where

import Cbpv
import Cbpv.Hom
import Cbpv.Sort
import Data.Kind
import Prelude hiding ((.), id, fst, snd)

inline :: Closed @SetTag a b -> Closed a b
inline x = Closed (out (fold x))

into :: Hom k a b -> Expr k a b
into x = Pure x

out :: Expr k a b -> Hom k a b
out x = case x of
  Pure x -> x

  Push x -> push (out x)
  Pop f -> pop (\x -> out (f (into x)))

  Lift x -> lift (out x)
  Kappa f -> kappa (\x -> out (f (into x)))

data Expr (k :: Set -> Set -> Type) (a :: Sort t) (b :: Sort t) where
  Pure :: Hom k a b -> Expr k a b
  Push :: (KnownSort a, KnownSort b) => Expr k Unit a -> Expr k b (a & b)
  Pop :: (KnownSort a, KnownSort b, KnownSort c) => (Expr f Unit a -> Expr f b c) -> Expr f (a & b) c

  Kappa :: (KnownSort a, KnownSort b, KnownSort c) => (Expr k Unit a -> Expr k b c) -> Expr k (a * b) c
  Lift :: (KnownSort a, KnownSort b) => Expr k Unit a -> Expr k b (a * b)

instance Category (Expr f) where
  id = into id

  Kappa f . Lift x = f x
  Pop f . Push x = f x

  f . g = into (out f . out g)

instance Stack (Expr f) where

instance Code (Expr g) where
  unit = into unit

  lift = Lift
  kappa = Kappa

instance Cbpv (Expr f) (Expr f) where
  thunk f = into (thunk $ \x -> out (f (into x)))
  force x = into (force (out x))

  push = Push
  pop = Pop

  pass x = into (pass (out x))
  zeta f = into (zeta $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant pkg name = into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
  cbpvIntrinsic x = into (cbpvIntrinsic x)
