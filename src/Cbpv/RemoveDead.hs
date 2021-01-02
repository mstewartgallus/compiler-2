{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Simplify code of the sort unit . x to unit
module Cbpv.RemoveDead (removeDead) where

import Cbpv
import Cbpv.Hom
import Cbpv.Sort
import Data.Kind
import Prelude hiding ((.), id, fst, snd)

removeDead :: Closed @SetTag a b -> Closed a b
removeDead x = Closed (out (fold x))

into :: Hom k a b -> Expr k a b
into x = Pure x

out :: Expr k a b -> Hom k a b
out x = case x of
  Pure x -> x
  Unit -> unit

data Expr (k :: Set -> Set -> Type) (a :: Sort t) (b :: Sort t) where
  Unit :: KnownSort a => Expr k a Unit
  Pure :: Hom k a b -> Expr k a b

instance Category (Expr f) where
  id = into id
  Unit . _ = Unit
  f . g = into (out f . out g)

instance Stack (Expr f) where

instance Code (Expr g) where
  unit = Unit

  fst = into fst
  snd = into snd
  x &&& y = into (out x &&& out y)

instance Cbpv (Expr f) (Expr f) where
  thunk f = into (thunk $ \x -> out (f (into x)))
  force x = into (force (out x))

  lift f x = into (lift (out f) (out x))
  pop f = into (pop $ \x -> out (f (into x)))

  pass f x = into (pass (out f) (out x))
  zeta f = into (zeta $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant pkg name = into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
  cbpvIntrinsic x = into (cbpvIntrinsic x)
