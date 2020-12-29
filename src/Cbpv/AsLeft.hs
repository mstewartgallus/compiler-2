{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

-- | Reassociate (f . g) . h to f . (g . h)
module Cbpv.AsLeft (asLeft) where

import Cbpv
import Control.Category
import Cbpv.Hom
import Cbpv.Sort
import Prelude hiding ((.), id, fst, snd)

asLeft :: Closed @SetTag a b -> Closed a b
asLeft x = Closed (out (fold x))

into :: k a b -> Path k a b
into x = x :.: Id

out :: Category k => Path k a b -> k a b
out x = case x of
  Id -> id
  f :.: g -> f . out g

data Path k a b where
  Id :: Path k a a
  (:.:) :: k b c -> Path k a b -> Path k a c

instance Category k => Category (Path k) where
  id = Id
  Id . f = f
  (f :.: g) . h = f :.: (g . h)

instance Cbpv f g => Stack (Path f) where

instance Cbpv f g => Code (Path g) where
  unit = into unit
  x &&& y = into (out x &&& out y)
  fst = into fst
  snd = into snd

instance Cbpv f g => Cbpv (Path f) (Path g) where
  thunk t f = into (thunk t $ \x -> out (f (into x)))
  force x = into (force (out x))

  lift x = into (lift (out x))
  pop t f = into (pop t $ \x -> out (f (into x)))

  pass x = into (pass (out x))
  zeta t f = into (zeta t $ \x -> out (f (into x)))

  u64 n = into (u64 n)
  constant t pkg name = into (constant t pkg name)
  cccIntrinsic x = into (cccIntrinsic x)
  cbpvIntrinsic x = into (cbpvIntrinsic x)
