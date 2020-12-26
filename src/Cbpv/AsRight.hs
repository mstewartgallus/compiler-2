{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

-- | Reassociate f . (g . h) to (f . g) . h
module Cbpv.AsRight (asRight) where

import Cbpv
import Control.Category
import Cbpv.Hom
import Cbpv.Sort
import Prelude hiding ((.), id)

asRight :: Closed @SetTag a b -> Closed a b
asRight x = Closed (out (fold x))

into :: k a b -> Path k a b
into x = Id :.: x

out :: Category k => Path k a b -> k a b
out x = case x of
  Id -> id
  f :.: g -> out f . g

data Path k a b where
  Id :: Path k a a
  (:.:) :: Path k b c -> k a b -> Path k a c

instance Category k => Category (Path k) where
  id = Id
  f . Id = f
  f . (g :.: h) = (f . g) :.: h

instance Cbpv f g => Stack (Path f) where

instance Cbpv f g => Code (Path g) where
  unit = into unit

  whereIsK f x = into (whereIsK (out f) (out x))
  kappa t f = into (kappa t $ \x -> out (f (into x)))

instance Cbpv f g => Cbpv (Path f) (Path g) where
  thunk x = into (thunk (out x))
  force x = into (force (out x))

  whereIs f x = into (whereIs (out f) (out x))
  pop t f = into (pop t $ \x -> out (f (into x)))

  app f x = into (app (out f) (out x))
  zeta t f = into (zeta t $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant t pkg name = into (constant t pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
  cbpvIntrinsic x = into (cbpvIntrinsic x)