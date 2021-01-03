{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Optimize tuples
module Pointless.Tuples (tuples) where

import Pointless
import Pointless.Hom
import Cbpv.Sort
import Data.Kind
import Prelude hiding ((.), id, fst, snd, curry, uncurry, drop)

tuples :: Hom @SetTag a b -> Hom a b
tuples x = out (fold x)

into :: Hom a b -> Expr a b
into x = Pure x

out :: Expr a b -> Hom a b
out x = case x of
  Pure x -> x
  Fst -> fst
  Snd -> snd
  Fanout x y -> out x &&& out y

data Expr (a :: Sort t) (b :: Sort t) where
  Fanout :: (KnownSort a, KnownSort b, KnownSort c) => Expr c a -> Expr c b -> Expr c (a * b)
  Fst :: (KnownSort a, KnownSort b) => Expr (a * b) a
  Snd :: (KnownSort a, KnownSort b) => Expr (a * b) b
  Pure :: Hom a b -> Expr a b

instance Category Expr where
  id = into id

  Fst . Fanout x _ = x
  Snd . Fanout _ x = x
  Fanout x y . f = (x . f) &&& (y . f)
  f . g = into (out f . out g)

instance Stack Expr where

instance Code Expr where
  unit = into unit
  fst = Fst
  snd = Snd

  Fst &&& Snd = id
  x &&& y = Fanout x y

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
