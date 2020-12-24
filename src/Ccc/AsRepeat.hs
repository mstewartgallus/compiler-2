module Ccc.AsRepeat (Expr, repeat) where

import Ccc
import qualified Ccc.AsSimplified as AsSimplified
import Control.Category
import Ccc.Type
import Ccc.HasExp
import Ccc.HasProduct
import Ccc.HasUnit
import Ccc.HasSum
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
  f . g = E (out f . out g) (step f . step g)

instance HasUnit f => HasUnit (Expr f) where
  unit = E unit unit

instance HasProduct f => HasProduct (Expr f) where
  lift f = E (lift (out f)) (lift (step f))

  kappa t f = E {
      out = kappa t $ \x -> out (f (E x undefined)),
      step = kappa t $ \x -> step (f (E undefined x))
           }

instance HasExp f => HasExp (Expr f) where
  pass f = E (pass (out f)) (pass (step f))

  zeta t f = E {
      out = zeta t $ \x -> out (f (E x undefined)),
      step = zeta t $ \x -> step (f (E undefined x))
           }

instance HasSum f => HasSum (Expr f) where
  absurd = E absurd absurd
  f ||| g = E (out f ||| out g) (step f ||| step g)
  left = E left left
  right = E right right

instance Ccc f => Ccc (Expr f) where
  u64 x = E (u64 x) (u64 x)
  constant t pkg name = E (constant t pkg name) (constant t pkg name)
  cccIntrinsic x = E (cccIntrinsic x) (cccIntrinsic x)
