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
import Control.Category
import Cbpv.Hom
import Cbpv.Sort
import Data.Kind
import Prelude hiding ((.), id)

removeDead :: Closed @SetTag a b -> Closed a b
removeDead x = Closed (out (fold x))

into :: Hom k a b -> Expr k a b
into x = Pure x

out :: Expr k a b -> Hom k a b
out x = case x of
  Pure x -> x
  Unit -> unit

data Expr (k :: Set -> Set -> Type) (a :: Sort t) (b :: Sort t) where
  Unit :: Expr k a Unit
  Pure :: Hom k a b -> Expr k a b

instance Category (Expr f) where
  id = into id
  Unit . _ = Unit
  f . g = into (out f . out g)

instance Stack (Expr f) where

instance Code (Expr g) where
  unit = Unit

  whereIsK Unit _ = Unit
  whereIsK f x = into (whereIsK (out f) (out x))
  kappa t f = into (kappa t $ \x -> out (f (into x)))

instance Cbpv (Expr f) (Expr f) where
  thunk x = into (thunk (out x))
  force x = into (force (out x))

  whereIs f x = into (whereIs (out f) (out x))
  pop t f = into (pop t $ \x -> out (f (into x)))

  app f x = into (app (out f) (out x))
  zeta t f = into (zeta t $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant t pkg name = into (constant t pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
  cbpvIntrinsic x = into (cbpvIntrinsic x)
