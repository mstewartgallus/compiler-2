module Lambda.AsOpt (Expr, opt) where

import Lambda
import qualified Lambda.AsSimplified as AsSimplified
import Control.Category
import Lambda.Type
import Lambda.HasExp
import Lambda.HasProduct
import Lambda.HasSum
import Prelude hiding ((.), id, curry, uncurry, Monad (..))

data Expr f a b = E {
  out :: f a b,
  step :: Expr (AsSimplified.Expr f) a b
  }

opt :: Expr f a b -> f a b
opt = loop 10

loop :: Int -> Expr f a b -> f a b
loop n x | n == 0 = out x
         | otherwise = AsSimplified.simplify (loop (n - 1) (step x))

instance Category f => Category (Expr f) where
  id = E id id
  f . g = me where
    me = E {
      out = out f . out g,
      step = step f . step g
      }
instance HasProduct f => HasProduct (Expr f) where
  unit = E unit unit
  f &&& g = me where
    me = E {
      out = out f &&& out g,
      step = step f &&& step g
      }
  first = E first first
  second = E second second
instance HasSum f => HasSum (Expr f) where
  absurd = E absurd absurd
  f ||| g = me where
    me = E {
      out = out f ||| out g,
      step = step f ||| step g
      }
  left = E left left
  right = E right right
instance HasExp f => HasExp (Expr f) where
  uncurry f = me where
    me = E {
      out = uncurry (out f),
      step = uncurry (step f)
      }
  curry f = me where
    me = E {
      out = curry (out f),
      step = curry (step f)
      }
instance Lambda f => Lambda (Expr f) where
  u64 x = E (u64 x) (u64 x)
  add = E add add
