{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Simplify code of the sort unit . x to unit
module Pointless.RemoveDead (removeDead) where

import Pointless
import Pointless.Hom
import Cbpv.Sort
import Data.Kind
import Prelude hiding ((.), id, fst, snd, curry, uncurry, drop)

removeDead :: Hom @SetTag a b -> Hom a b
removeDead x = out (fold x)

into :: Hom a b -> Expr a b
into x = Pure x

out :: Expr a b -> Hom a b
out x = case x of
  Pure x -> x
  Unit -> unit

data Expr (a :: Sort t) (b :: Sort t) where
  Unit :: KnownSort a => Expr a Unit
  Pure :: Hom a b -> Expr a b

instance Category Expr where
  id = into id
  Unit . _ = Unit
  f . g = into (out f . out g)

instance Stack Expr where

instance Code Expr where
  unit = Unit
  fst = into fst
  snd = into snd
  x &&& y = into (out x &&& out y)

instance Pointless Expr Expr where
  lmapStack x = into (lmapStack (out x))
  rmapStack x = into (rmapStack (out x))

  thunk x = into (thunk (out x))
  force x = into (force (out x))

  drop = into drop
  inStack = into inStack
  push = into push
  pop = into pop

  curry x = into (curry (out x))
  uncurry x = into (uncurry (out x))

  u64 n = into (u64 n)
  constant pkg name = into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
  cbpvIntrinsic x = into (cbpvIntrinsic x)
