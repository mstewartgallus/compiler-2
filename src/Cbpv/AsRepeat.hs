{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.AsRepeat (Stk, Cde, repeat) where

import Cbpv
import qualified Cbpv.AsSimplified as AsSimplified
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, curry, uncurry, Monad (..), repeat)

data Stk f g a b = K {
  outK :: f a b,
  stepK :: Stk (AsSimplified.Stk f g) (AsSimplified.Cde f g) a b
  }
data Cde f g a b = C {
  outC :: g a b,
  stepC :: Cde (AsSimplified.Stk f g) (AsSimplified.Cde f g) a b
  }

repeat :: Int -> Cde f g a b -> g a b
repeat = loop

loop :: Int -> Cde f g a b -> g a b
loop n x | n == 0 = outC x
         | otherwise = AsSimplified.simplify (loop (n - 1) (stepC x))

instance (Category f, Category g) => Category (Stk f g) where
  id = K id id
  f . g = me where
    me = K {
      outK = outK f . outK g,
      stepK = stepK f . stepK g
      }
instance (Category f, Category g) => Category (Cde f g) where
  id = C id id
  f . g = me where
    me = C {
      outC = outC f . outC g,
      stepC = stepC f . stepC g
      }

instance Cbpv f g => Code (Cde f g) where
  unit = C unit unit

  absurd = C absurd absurd
  f ||| g = me where
    me = C {
      outC = outC f ||| outC g,
      stepC = stepC f ||| stepC g
      }
  left = C left left
  right = C right right

  lift f = me where
    me = C {
      outC = lift (outC f),
      stepC = lift (stepC f)
      }

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

  return f = me where
    me = K {
      outK = return (outC f),
      stepK = return (stepC f)
      }
  pass f = me where
    me = K {
      outK = pass (outC f),
      stepK = pass (stepC f)
      }
  push f = me where
    me = K {
      outK = push (outC f),
      stepK = push (stepC f)
      }

  be x f = C (be (outC x) outF) (be (stepC x) stepF) where
    outF x' = outC (f (C x' undefined))
    stepF x' = stepC (f (C undefined x'))

  letTo x f = K (letTo (outK x) outF) (letTo (stepK x) stepF) where
    outF x' = outK (f (C x' undefined))
    stepF x' = stepK (f (C undefined x'))

  zeta t f = K (zeta t outF) (zeta t stepF) where
    outF x' = outK (f (C x' undefined))
    stepF x' = stepK (f (C undefined x'))
  pop t f = K (pop t outF) (pop t stepF) where
    outF x' = outK (f (C x' undefined))
    stepF x' = stepK (f (C undefined x'))

  u64 x = C (u64 x) (u64 x)

  constant t pkg name = K (constant t pkg name) (constant t pkg name)
  lambdaIntrinsic x = C (lambdaIntrinsic x) (lambdaIntrinsic x)
  cbpvIntrinsic x = C (cbpvIntrinsic x) (cbpvIntrinsic x)
