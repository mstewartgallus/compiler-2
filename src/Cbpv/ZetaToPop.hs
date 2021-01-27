{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Convert pass x . zeta f to pop f . push x
module Cbpv.ZetaToPop (zetaToPop) where

import Cbpv
import Cbpv.Hom
import Cbpv.Sort
import Data.Kind
import Prelude hiding ((.), id, fst, snd)

zetaToPop :: Term stack code => code a b -> Closed a b
zetaToPop x = Closed (out (foldCode x))

into :: Hom k a b -> Expr k a b
into x = Pure x

out :: Expr k a b -> Hom k a b
out x = case x of
  Pure x -> x
  Pass x -> pass (out x)
  Zeta f -> zeta (\x -> out (f (into x)))

data Expr (k :: Set -> Set -> Type) (a :: t) (b :: t) where
  Pure :: Hom k a b -> Expr k a b
  Pass :: (KnownSet a, KnownAlgebra b) => Expr k Unit a -> Expr k (a ~> b) b
  Zeta :: (KnownSet a, KnownAlgebra b, KnownAlgebra c) => (Expr f Unit a -> Expr f b c) -> Expr f b (a ~> c)

instance Stack (Expr f) where
  skip = into skip
  Pass x <<< Zeta f = pop f <<< push x
  f <<< g = into (out f <<< out g)

instance Code (Expr g) where
  id = into id
  f . g = into (out f . out g)

  unit = into unit
  fst = into fst
  snd = into snd
  x &&& y = into (out x &&& out y)

instance Cbpv (Expr f) (Expr f) where
  thunk f = into (thunk $ \x -> out (f (into x)))
  force x = into (force (out x))

  push x = into (push (out x))
  pop f = into (pop $ \x -> out (f (into x)))

  pass = Pass
  zeta = Zeta

  u64 n = into (u64 n)
  constant pkg name = into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
  cbpvIntrinsic x = into (cbpvIntrinsic x)
