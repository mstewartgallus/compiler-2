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

inline :: Closed @Set a b -> Closed a b
inline x = Closed (out (fold x))

into :: Hom k a b -> Expr k a b
into x = Pure x

out :: Expr k a b -> Hom k a b
out x = case x of
  Pure x -> x

  Push x -> push (out x)
  Pop f -> pop (\x -> out (f (into x)))

data Expr (k :: Set -> Set -> Type) (a :: t) (b :: t) where
  Pure :: Hom k a b -> Expr k a b

  Push :: (KnownSet a, KnownAlgebra b) => Expr k Unit a -> Expr k b (a & b)
  Pop :: (KnownSet a, KnownAlgebra b, KnownAlgebra c) => (Expr f Unit a -> Expr f b c) -> Expr f (a & b) c

instance Stack (Expr f) where
  skip = into skip
  Pop f <<< Push x = f x
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

  push = Push
  pop = Pop

  pass x = into (pass (out x))
  zeta f = into (zeta $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant pkg name = into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
  cbpvIntrinsic x = into (cbpvIntrinsic x)
