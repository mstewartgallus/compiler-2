{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.AsCost (Stack, Code, cost) where

import Cbpv
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id)

newtype Stack (a :: Algebra) (b :: Algebra) = K Int

newtype Code (a :: Set) (b :: Set) = C Int

cost :: Code a b -> Int
cost (C v) = v

instance Category Stack where
  id = K 0
  K f . K g = K (f + g)

instance Category Code where
  id = C 0
  C f . C g = C (f + g)

instance Cbpv Stack Code where
  to (K f) (K x) = K (1 + f + x)
  return (C f) = K (1 + f)

  thunk (K f) = C (1 + f)
  force (C f) = K (1 + f)

  unit = C 0
  C f &&& C g = C (1 + f + g)
  first = C 1
  second = C 1

  absurd = C 0
  C f ||| C g = C (1 + f + g)
  left = C 1
  right = C 1

  assocOut = K 1
  assocIn = K 1

  curry (K f) = K (1 + f)
  uncurry (K f) = K (1 + f)

  u64 x = C 0
  add = C 0
  addLazy = K 0
