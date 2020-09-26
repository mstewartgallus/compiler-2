{-# LANGUAGE MultiParamTypeClasses #-}

-- | Remove duplicate force/thunk pairs
module Cbpv.AsOpt (Stack, Code, opt) where

import Cbpv
import qualified Cbpv.AsSimplified as AsSimplified
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, curry, uncurry, Monad (..))

data Stack f g a b = K {
  outK :: f a b,
  stepK :: Stack (AsSimplified.Stack f g) (AsSimplified.Code f g) a b
  }
data Code f g a b = C {
  outC :: g a b,
  stepC :: Code (AsSimplified.Stack f g) (AsSimplified.Code f g) a b
  }

opt :: Code f g a b -> g a b
opt = loop 10

loop :: Int -> Code f g a b -> g a b
loop n x | n == 0 = outC x
         | otherwise = AsSimplified.simplify (loop (n - 1) (stepC x))

instance (Category f, Category g) => Category (Stack f g) where
  id = K { outK = id,stepK = id}
  f . g = me where
    me = K {
      outK = outK f . outK g,
      stepK = stepK f . stepK g
      }
instance (Category f, Category g) => Category (Code f g) where
  id = C {outC = id,stepC = id}
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

  pop = K { outK = pop, stepK = pop }
  push = K { outK = push, stepK = push }

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

  u64 x = C (u64 x) (u64 x)

  constant t pkg name = K (constant t pkg name) (constant t pkg name)
