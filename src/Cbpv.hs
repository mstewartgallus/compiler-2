{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cbpv (Stack (..), Code (..), Cbpv (..), Intrinsic (..)) where

import Cbpv.Sort
import Control.Category
import Data.Word (Word64)
import qualified Hoas.Type as Hoas
import qualified Lambda as Lambda
import qualified Lambda.Type as Lambda
import Prelude hiding (curry, id, return, uncurry, (.), (<*>))

-- |
-- As opposed to the usual monadic interface call by push value is based
-- around adjoint functors on two different categories.
--
-- There is a different formulation using oblique morphisms and an
-- indexed category instead of using the asymmetric tensor but was
-- difficult to work with.
--
-- Paul Blain Levy. "Call-by-Push-Value: A Subsuming Paradigm".
class Category stack => Stack stack where
  foo :: stack (a & env) b -> stack env (a ~> b)

class Category code => Code code where
  unit :: code x Unit
  kappa :: SSet a -> (code Unit a -> code b c) -> code (a * b) c
  lift :: code Unit a -> code b (a * b)

  absurd :: code Void x
  (|||) :: code a c -> code b c -> code (a + b) c
  left :: code a (a + b)
  right :: code b (a + b)

class (Stack stack, Code code) => Cbpv stack code | stack -> code, code -> stack where
  -- | fixme.. deprecate
  return :: code env a -> stack (env & x) (a & x)
  return x = pop undefined (\env -> push (x . env))

  thunk :: stack (F x) y -> code x (U y)
  force :: code x (U y) -> stack (F x) y

  pop :: SSet a -> (code Unit a -> stack b c) -> stack (a & b) c
  push :: code Unit a -> stack b (a & b)

  zeta :: SSet a -> (code Unit a -> stack b c) -> stack b (a ~> c)
  pass :: code Unit a -> stack (a ~> b) b

  u64 :: Word64 -> code Unit U64

  constant :: Hoas.ST a -> String -> String -> stack (F Unit) (AsAlgebra (Lambda.AsObject a))
  lambdaIntrinsic :: Lambda.Intrinsic a b -> code (U (AsAlgebra a)) (U (AsAlgebra b))
  cbpvIntrinsic :: Intrinsic a b -> code a b

  add :: code (U64 * U64) U64
  add = cbpvIntrinsic AddIntrinsic

data Intrinsic a b where
  AddIntrinsic :: Intrinsic (U64 * U64) U64

instance Show (Intrinsic a b) where
  show x = case x of
    AddIntrinsic -> "$add"

infixl 9 |||
