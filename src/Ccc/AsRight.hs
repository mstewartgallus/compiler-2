{-# LANGUAGE GADTs #-}

-- | Reassociate f . (g . h) to (f . g) . h
module Ccc.AsRight (asRight) where

import Ccc
import Dict
import Ccc.Hom
import Ccc.Type
import qualified Lam.Type as Lam
import Prelude hiding ((.), id)

asRight :: Term hom => hom a b -> Closed a b
asRight x = Closed (out (foldTerm x))

into :: (KnownT a, KnownT b) => Hom k a b -> Path k a b
into x = Id :.: x

out :: Path k a b -> Hom k a b
out x = case x of
  Id -> id
  f :.: g -> out f . g

data Path k a b where
  Id :: KnownT a => Path k a a
  (:.:) :: (KnownT a, KnownT b, KnownT c) => Path k b c -> Hom k a b -> Path k a c

instance Ccc (Path k) where
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

constant' :: Lam.KnownT a => ObjectOf KnownDict a -> String -> String -> Path k Unit (AsObject a)
constant' a pkg name = case toKnownT (asObject a) of
  Dict -> into (constant pkg name)
