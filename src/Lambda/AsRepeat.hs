module Lambda.AsRepeat (Expr, repeat) where

import Lambda
import qualified Lambda.AsSimplified as AsSimplified
import Control.Category
import Lambda.Type
import Lambda.HasExp
import Lambda.HasLet
import Lambda.HasProduct
import Lambda.HasSum
import Prelude hiding ((.), id, curry, uncurry, Monad (..), repeat)

data Expr f a b = E {
  out :: f a b,
  step :: Expr (AsSimplified.Expr f) a b
  }

repeat :: Int -> Expr f a b -> f a b
repeat = loop

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
instance HasLet f => HasLet (Expr f) where
  be t f = me where
    me = E {
      out = be t $ \x' -> out (f (E x' undefined)),
      step = be t $ \x' -> step (f (E undefined x'))
           }
instance Lambda f => Lambda (Expr f) where
  u64 x = E (u64 x) (u64 x)
  constant t pkg name = E (constant t pkg name) (constant t pkg name)
  lambdaConstant t pkg name = E (lambdaConstant t pkg name) (lambdaConstant t pkg name)
