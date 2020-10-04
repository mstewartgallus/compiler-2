{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.AsRepeat (Stack, Code, repeat) where

import Cbpv
import qualified Cbpv.AsSimplified as AsSimplified
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, curry, uncurry, Monad (..), repeat)

data Stack f g a b = K {
  outK :: f a b,
  stepK :: Stack (AsSimplified.Stack f g) (AsSimplified.Code f g) a b
  }
data Code f g a b = C {
  outC :: g a b,
  stepC :: Code (AsSimplified.Stack f g) (AsSimplified.Code f g) a b
  }

repeat :: Int -> Code f g a b -> g a b
repeat = loop

loop :: Int -> Code f g a b -> g a b
loop n x | n == 0 = outC x
         | otherwise = AsSimplified.simplify (loop (n - 1) (stepC x))

instance (Category f, Category g) => Category (Stack f g) where
  id = K id id
  f . g = me where
    me = K {
      outK = outK f . outK g,
      stepK = stepK f . stepK g
      }
instance (Category f, Category g) => Category (Code f g) where
  id = C id id
  f . g = me where
    me = C {
      outC = outC f . outC g,
      stepC = stepC f . stepC g
      }

instance Cbpv f g => Cbpv (Stack f g) (Code f g) where
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

  unit = C unit unit
  f &&& g = me where
    me = C {
      outC = outC f &&& outC g,
      stepC = stepC f &&& stepC g
      }
  first = C first first
  second = C second second

  absurd = C absurd absurd
  f ||| g = me where
    me = C {
      outC = outC f ||| outC g,
      stepC = stepC f ||| stepC g
      }
  left = C left left
  right = C right right

  pop = K pop pop
  push = K push push

  uncurry f = me where
    me = K {
      outK = uncurry (outK f),
      stepK = uncurry (stepK f)
      }
  curry f = me where
    me = K {
      outK = curry (outK f),
      stepK = curry (stepK f)
      }

  be x f = C (be (outC x) outF) (be (stepC x) stepF) where
    outF x' = outC (f (C x' undefined))
    stepF x' = stepC (f (C undefined x'))

  u64 x = C (u64 x) (u64 x)

  constant t pkg name = K (constant t pkg name) (constant t pkg name)
  lambdaConstant t pkg name = K (lambdaConstant t pkg name) (lambdaConstant t pkg name)
  cbpvConstant t pkg name = K (cbpvConstant t pkg name) (cbpvConstant t pkg name)
