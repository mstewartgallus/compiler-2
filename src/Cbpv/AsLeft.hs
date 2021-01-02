{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

-- | Reassociate (f . g) . h to f . (g . h)
module Cbpv.AsLeft (asLeft) where

import Cbpv
import Cbpv.Hom
import Cbpv.Sort
import Dict
import qualified Ccc
import qualified Ccc.Type as Ccc
import qualified Lam.Type as Lam
import Prelude hiding ((.), id, fst, snd)

asLeft :: Closed @SetTag a b -> Closed a b
asLeft x = Closed (out (fold x))

into :: (KnownSort a, KnownSort b) => k a b -> Path k a b
into x = x :.: Id

out :: Category k => Path k a b -> k a b
out x = case x of
  Id -> id
  f :.: g -> f . out g

data Path k a b where
  Id :: KnownSort a => Path k a a
  (:.:) :: (KnownSort a, KnownSort b, KnownSort c) => k b c -> Path k a b -> Path k a c

instance Category k => Category (Path k) where
  id = Id
  Id . f = f
  (f :.: g) . h = f :.: (g . h)

instance Cbpv f g => Stack (Path f) where

instance Cbpv f g => Code (Path g) where
  unit = into unit
  kappa f = into (kappa $ \x -> (out (f (into x))))
  lift x = into (lift (out x))

instance Cbpv f g => Cbpv (Path f) (Path g) where
  thunk f = into (thunk $ \x -> out (f (into x)))
  force x = into (force (out x))

  push x = into (push (out x))
  pop f = into (pop $ \x -> out (f (into x)))

  pass x = into (pass (out x))
  zeta f = into (zeta $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant = constant' Lam.inferT
  cccIntrinsic = cccIntrinsic' Ccc.inferT Ccc.inferT
  cbpvIntrinsic x = into (cbpvIntrinsic x)

constant' :: (Lam.KnownT a, Cbpv f g) => Lam.ST a -> String -> String -> Path f (F Unit) (AsAlgebra (Ccc.AsObject a))
constant' a pkg name = case toKnownSort (asAlgebra (Ccc.asObject a)) of
  Dict -> into (constant pkg name)

cccIntrinsic' :: Cbpv f g => Ccc.ST a -> Ccc.ST b -> Ccc.Intrinsic a b -> Path f (AsAlgebra a) (AsAlgebra b)
cccIntrinsic' a b x = case (Ccc.toKnownT a, Ccc.toKnownT b, toKnownSort (asAlgebra a), toKnownSort (asAlgebra b)) of
  (Dict, Dict, Dict, Dict) -> into (cccIntrinsic x)
