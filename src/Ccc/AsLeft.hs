{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

-- | Reassociate  (f . g) . h to f . (g . h)
module Ccc.AsLeft (asLeft) where

import Dict
import Ccc
import Ccc.Hom
import Ccc.Type
import qualified Lam.Type as Lam
import Prelude hiding ((.), id)

asLeft :: Closed a b -> Closed a b
asLeft x = Closed (out (fold x))

into :: (KnownT a, KnownT b) => k a b -> Path k a b
into x = x :.: Id

out :: Ccc k => Path k a b -> k a b
out x = case x of
  Id -> id
  f :.: g -> f . out g

data Path k a b where
  Id :: KnownT a => Path k a a
  (:.:) :: (KnownT a, KnownT b, KnownT c) => k b c -> Path k a b -> Path k a c

instance Ccc k => Ccc (Path k) where
  id = Id
  Id . f = f
  (f :.: g) . h = f :.: (g . h)

  unit = into unit

  lift Id = into (lift unit)
  lift x = into (lift (out x))
  kappa f = into (kappa $ \x -> out (f (into x)))

  pass Id = into (pass unit)
  pass x = into (pass (out x))
  zeta f = into (zeta $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant pkg name = me where
    a = argOf me
    b = typeOf me
    me = case (toKnownT (asObject a), toKnownT (asObject b)) of
      (Dict, Dict) -> into (constant pkg name)
  cccIntrinsic x = into (cccIntrinsic x)

argOf :: Lam.KnownT a => Path k (AsObject a) b -> Lam.ST a
argOf _ = Lam.inferT

typeOf :: Lam.KnownT b => Path k a (AsObject b) -> Lam.ST b
typeOf _ = Lam.inferT
