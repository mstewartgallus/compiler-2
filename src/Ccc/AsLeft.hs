{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

-- | Reassociate  (f . g) . h to f . (g . h)
module Ccc.AsLeft (asLeft) where

import Ccc
import Ccc.Hom
import Ccc.Type
import Prelude hiding ((.), id)

asLeft :: Closed a b -> Closed a b
asLeft x = Closed (out (fold x))

into :: k a b -> Path k a b
into x = x :.: Id

out :: Ccc k => Path k a b -> k a b
out x = case x of
  Id -> id
  f :.: g -> f . out g

data Path k a b where
  Id :: Path k a a
  (:.:) :: k b c -> Path k a b -> Path k a c

instance Ccc k => Ccc (Path k) where
  id = Id
  Id . f = f
  (f :.: g) . h = f :.: (g . h)

  unit = into unit

  lift Id = into (lift unit)
  lift x = into (lift (out x))
  kappa t f = into (kappa t $ \x -> out (f (into x)))

  pass Id = into (pass unit)
  pass x = into (pass (out x))
  zeta t f = into (zeta t $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant t pkg name = into (constant t pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
