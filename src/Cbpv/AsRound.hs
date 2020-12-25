{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}

-- | Run one round of passes
module Cbpv.AsRound (Stk, Cde, round) where

import Cbpv
import qualified Cbpv.AsSimplified as AsSimplified
import qualified Cbpv.AsLeft as AsLeft
import Control.Category
import Cbpv.Sort
import qualified Ccc.Type as Ccc
import qualified Ccc as Ccc
import Prelude hiding ((.), id, round)

newtype Stk f g a b = K (AsLeft.Stk (AsSimplified.Stk f g) (AsSimplified.Cde f g) a b)
newtype Cde f g a b = C (AsLeft.Cde (AsSimplified.Stk f g) (AsSimplified.Cde f g) a b)

round :: Cde f g a b -> g a b
round (C x) = AsSimplified.simplify (AsLeft.asLeft x)

instance (Category f, Category g) => Category (Stk f g) where
  id = K id
  K f . K g = K (f . g)

instance (Category f, Category g) => Category (Cde f g) where
  id = C id
  C f . C g = C (f . g)

instance Cbpv f g => Code (Cde f g) where
  unit = C unit

  whereIsK (C f) (C x) = C (whereIsK f x)
  kappa t f = C $ kappa t $ \x -> case f (C x) of
    C y -> y

instance Cbpv f g => Stack (Stk f g) where

instance Cbpv f g => Cbpv (Stk f g) (Cde f g) where
  thunk (K f) = C (thunk f)
  force (C f) = K (force f)

  pass (C f) = K (pass f)
  push (C f) = K (push f)

  zeta t f = K $ zeta t $ \x -> case f (C x) of
    K y -> y
  pop t f = K $ pop t $ \x -> case f (C x) of
    K y -> y

  u64 x = C (u64 x)

  constant t pkg name = K (constant t pkg name)
  cccIntrinsic x = C (cccIntrinsic x)
  cbpvIntrinsic x = C (cbpvIntrinsic x)
