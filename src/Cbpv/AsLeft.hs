{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

-- | Reassociate  (f . g) . h to  f . (g . h)
module Cbpv.AsLeft (asLeft) where

import Cbpv
import Cbpv.Hom
import Dict
import Cbpv.Sort
import qualified Lam.Type as Lam
import qualified Ccc.Type as Ccc
import qualified Ccc
import Prelude hiding ((.), id, fst, snd)

asLeft :: Term stack code => code a b -> Closed a b
asLeft x = Closed (outc (foldCode x))

inc :: (KnownSet a, KnownSet b) => code a b -> PC code a b
inc x = x :.: Id

outc :: Cbpv stack code => PC code a b -> code a b
outc x = case x of
  Id -> id
  f :.: Id -> f
  f :.: g -> f . outc g

ink :: (KnownAlgebra a, KnownAlgebra b) => stack a b -> PK stack a b
ink x = x :<<<: Skip

outk :: Cbpv stack code => PK stack a b -> stack a b
outk x = case x of
  Skip -> skip
  f :<<<: Skip -> f
  f :<<<: g -> f <<< outk g

data PC k a b where
  Id :: KnownSet a => PC k a a
  (:.:) :: (KnownSet a, KnownSet b, KnownSet c) => k b c -> PC k a b -> PC k a c

data PK stack a b where
  Skip :: KnownAlgebra a => PK stack a a
  (:<<<:) :: (KnownAlgebra a, KnownAlgebra b, KnownAlgebra c) => k b c -> PK k a b -> PK k a c

instance Cbpv stack code => Code (PC code) where
  id = Id

  Id . f = f
  (f :.: g) . h = f :.: (g . h)

  unit = inc unit

  x &&& y = inc (outc x &&& outc y)
  fst = inc fst
  snd = inc snd

instance Cbpv stack code => Stack (PK stack) where
  skip = Skip

  Skip <<< f = f
  (f :<<<: g) <<< h = f :<<<: (g <<< h)

instance Cbpv stack code => Cbpv (PK stack) (PC code) where
  thunk f = inc (thunk (\x -> outk (f (inc x))))
  force x = ink (force (outc x))

  pop f = ink (pop (\x -> outk (f (inc x))))
  push x = ink (push (outc x))

  zeta f = ink (zeta (\x -> outk (f (inc x))))
  pass x = ink (pass (outc x))

  u64 n = inc (u64 n)
  constant = constant' Lam.inferT

  cccIntrinsic = cccIntrinsic' Ccc.inferT Ccc.inferT
  cbpvIntrinsic x = inc (cbpvIntrinsic x)

constant' :: (Cbpv stack code, Lam.KnownT a) => Ccc.ObjectOf a -> String -> String -> PC code Unit (U (AsAlgebra (Ccc.AsObject a)))
constant' (Ccc.ObjectOf Dict) = constant'' Ccc.inferT

constant'' :: (Cbpv stack code, Lam.KnownT a) => AlgebraOf (Ccc.AsObject a) -> String -> String -> PC code Unit (U (AsAlgebra (Ccc.AsObject a)))
constant'' (AlgebraOf Dict) pkg name = inc (constant pkg name)

cccIntrinsic' :: (Cbpv stack code, Ccc.KnownT a, Ccc.KnownT b) => AlgebraOf a -> AlgebraOf b -> Ccc.Intrinsic a b -> PK stack (AsAlgebra a) (AsAlgebra b)
cccIntrinsic' (AlgebraOf Dict) (AlgebraOf Dict) x = ink (cccIntrinsic x)
