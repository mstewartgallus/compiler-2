{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

-- | Reassociate  f . (g . h) to  (f . g) . h
module Ccc.AsRight (asRight, AsRight) where

import Ccc
import Dict
import Ccc.Hom
import Ccc.Type
import qualified Lam.Type as Lam
import Prelude hiding ((.), id)

asRight :: Term hom => hom a b -> AsRight a b
asRight x = AsRight (foldTerm x)

newtype AsRight a b = AsRight (forall k. Ccc k => Path k a b)
instance Term AsRight where
  foldTerm (AsRight x) = out x

into :: (KnownT a, KnownT b) => k a b -> Path k a b
into x = Id :.: x

out :: Ccc k => Path k a b -> k a b
out x = case x of
  Id -> id
  f :.: g -> out f . g

data Path k a b where
  Id :: KnownT a => Path k a a
  (:.:) :: (KnownT a, KnownT b, KnownT c) => Path k b c -> k a b -> Path k a c

instance Ccc k => Ccc (Path k) where
  id = Id
  f . Id = f
  f . (g :.: h) = (f . g) :.: h

  unit = into unit

  lift x = into (lift (out x))
  kappa f = into (kappa $ \x -> out (f (into x)))

  pass x = into (pass (out x))
  zeta f = into (zeta $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant = constant' Lam.inferT
  cccIntrinsic x = into (cccIntrinsic x)

constant' :: (Ccc k, Lam.KnownT a) => ObjectOf a -> String -> String -> Path k Unit (AsObject a)
constant' (ObjectOf Dict) pkg name = into (constant pkg name)
