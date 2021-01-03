{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

-- | Reassociate  f . (g . h) to (f . g) . h
module Pointless.AsRight (asRight) where

import Pointless
import Pointless.Hom
import Cbpv.Sort
import Dict
import qualified Ccc
import qualified Ccc.Type as Ccc
import qualified Lam.Type as Lam
import Prelude hiding ((.), id, fst, snd, curry, uncurry, drop)

asRight :: Hom @SetTag a b -> Hom a b
asRight x = out (fold x)

into :: (KnownSort a, KnownSort b) => k a b -> Path k a b
into x = Id :.: x

out :: Category k => Path k a b -> k a b
out x = case x of
  Id -> id
  f :.: g -> out f . g

data Path k a b where
  Id :: KnownSort a => Path k a a
  (:.:) :: (KnownSort a, KnownSort b, KnownSort c) => Path k b c -> k a b -> Path k a c

instance Category k => Category (Path k) where
  id = Id
  f . Id = f
  f . (g :.: h) = (f . g) :.: h

instance Pointless f g => Stack (Path f) where

instance Pointless f g => Code (Path g) where
  unit = into unit
  x &&& y = into (out x &&& out y)
  fst = into fst
  snd = into snd

instance Pointless f g => Pointless (Path f) (Path g) where
  thunk x = into (thunk (out x))
  force x = into (force (out x))

  push = into push
  pop = into pop

  curry x = into (curry (out x))
  uncurry x = into (uncurry (out x))

  lmapStack x = into (lmapStack (out x))
  rmapStack x = into (rmapStack (out x))

  drop = into drop
  inStack = into inStack

  u64 n = into (u64 n)
  constant = constant' Lam.inferT
  cccIntrinsic = cccIntrinsic' Ccc.inferT Ccc.inferT
  cbpvIntrinsic x = into (cbpvIntrinsic x)

constant' :: (Lam.KnownT a, Pointless f g) => Lam.ST a -> String -> String -> Path g Unit (U (AsAlgebra (Ccc.AsObject a)))
constant' a pkg name = case toKnownSort (asAlgebra (Ccc.asObject a)) of
  Dict -> into (constant pkg name)

cccIntrinsic' :: Pointless f g => Ccc.ST a -> Ccc.ST b -> Ccc.Intrinsic a b -> Path f (AsAlgebra a) (AsAlgebra b)
cccIntrinsic' a b x = case (Ccc.toKnownT a, Ccc.toKnownT b, toKnownSort (asAlgebra a), toKnownSort (asAlgebra b)) of
  (Dict, Dict, Dict, Dict) -> into (cccIntrinsic x)
