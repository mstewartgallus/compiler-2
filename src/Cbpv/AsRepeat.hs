{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.AsRepeat (Stk, Cde, repeat) where

import Cbpv
import qualified Cbpv.AsRound as AsRound
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, curry, uncurry, Monad (..), repeat)

data Stk f g a b = K {
  outK :: f a b,
  stepK :: Stk (AsRound.Stk f g) (AsRound.Cde f g) a b
  }
data Cde f g a b = C {
  outC :: g a b,
  stepC :: Cde (AsRound.Stk f g) (AsRound.Cde f g) a b
  }

repeat :: Int -> Cde f g a b -> g a b
repeat = loop

loop :: Int -> Cde f g a b -> g a b
loop n x | n == 0 = outC x
         | otherwise = AsRound.round (loop (n - 1) (stepC x))

instance (Category f, Category g) => Category (Stk f g) where
  id = K id id
  f . g = K (outK f . outK g) (stepK f . stepK g)

instance (Category f, Category g) => Category (Cde f g) where
  id = C id id
  f . g = C (outC f . outC g) (stepC f . stepC g)

instance Cbpv f g => Code (Cde f g) where
  unit = C unit unit

  whereIsK f x = C (whereIsK (outC f) (outC x)) (whereIsK (stepC f) (stepC x))
  kappa t f = C (kappa t outF) (kappa t stepF) where
    outF x' = outC (f (C x' undefined))
    stepF x' = stepC (f (C undefined x'))

instance Cbpv f g => Stack (Stk f g) where

instance Cbpv f g => Cbpv (Stk f g) (Cde f g) where
  thunk f = me where
    me = C {
      outC = thunk (outK f),
      stepC = thunk (stepK f)
      }
  force f = me where
    me = K {
      outK = force (outC f),
      stepK = force (stepC f)
      }

  app f x = K (app (outK f) (outC x)) (app (stepK f) (stepC x))
  zeta t f = K (zeta t outF) (zeta t stepF) where
    outF x' = outK (f (C x' undefined))
    stepF x' = stepK (f (C undefined x'))

  whereIs f x = K (whereIs (outK f) (outC x)) (whereIs (stepK f) (stepC x))
  pop t f = K (pop t outF) (pop t stepF) where
    outF x' = outK (f (C x' undefined))
    stepF x' = stepK (f (C undefined x'))

  u64 x = C (u64 x) (u64 x)

  constant t pkg name = K (constant t pkg name) (constant t pkg name)
  cccIntrinsic x = C (cccIntrinsic x) (cccIntrinsic x)
  cbpvIntrinsic x = C (cbpvIntrinsic x) (cbpvIntrinsic x)
