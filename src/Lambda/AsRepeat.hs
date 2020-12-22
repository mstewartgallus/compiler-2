module Lambda.AsRepeat (Expr, repeat) where

import Lambda
import qualified Lambda.AsSimplified as AsSimplified
import Control.Category
import Lambda.Type
import Lambda.HasExp
import Lambda.HasProduct
import Lambda.HasUnit
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

instance HasUnit f => HasUnit (Expr f) where
  unit = E unit unit

instance HasProduct f => HasProduct (Expr f) where
  lift f = me where
    me = E {
      out = lift (out f),
      step = lift (step f)
      }

  kappa t f = me where
    me = E {
      out = kappa t $ \x -> out (f (E x undefined)),
      step = kappa t $ \x -> step (f (E undefined x))
           }

instance HasExp f => HasExp (Expr f) where
  zeta t f =  me where
    me = E {
      out = zeta t $ \x -> out (f (E x undefined)),
      step = zeta t $ \x -> step (f (E undefined x))
           }
  pass x = me where
    me = E {
      out = pass (out x),
      step = pass (step x)
           }

instance HasSum f => HasSum (Expr f) where
  absurd = E absurd absurd
  f ||| g = me where
    me = E {
      out = out f ||| out g,
      step = step f ||| step g
      }
  left = E left left
  right = E right right

instance Lambda f => Lambda (Expr f) where
  u64 x = E (u64 x) (u64 x)
  constant t pkg name = E (constant t pkg name) (constant t pkg name)
  lambdaIntrinsic x = E (lambdaIntrinsic x) (lambdaIntrinsic x)
