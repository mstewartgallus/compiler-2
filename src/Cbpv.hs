{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cbpv (Cbpv (..)) where

import Cbpv.Sort
import Control.Category
import Data.Word (Word64)
import qualified Hoas.Type as Hoas
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
class (Category stack, Category code) => Cbpv stack code | stack -> code, code -> stack where
  return :: code env a -> stack (F env) (F a)

  thunk :: stack (F x) y -> code x (U y)
  force :: code x (U y) -> stack (F x) y

  unit :: code x Unit
  (&&&) :: code env a -> code env b -> code env (a * b)
  first :: code (a * b) a
  second :: code (a * b) b

  absurd :: code Void x
  (|||) :: code a c -> code b c -> code (a + b) c
  left :: code a (a + b)
  right :: code b (a + b)

  pop :: stack (a & (b & c)) ((a * b) & c)
  push :: stack ((a * b) & c) (a & (b & c))

  curry :: stack (a & env) b -> stack env (a ~> b)
  uncurry :: stack env (a ~> b) -> stack (a & env) b

  be :: code x a -> (code Unit a -> code x c) -> code x c

  u64 :: Word64 -> code Unit U64

  constant :: Hoas.ST a -> String -> String -> stack (F Unit) (AsAlgebra (Lambda.AsObject a))
  lambdaConstant :: Lambda.ST a -> String -> String -> stack (F Unit) (AsAlgebra a)
  cbpvConstant :: SAlgebra a -> String -> String -> stack (F Unit) a

  add :: stack (F Unit) (U64 ~> (U64 ~> F U64))
  add = cbpvConstant (SU64 :-> (SU64 :-> (SU64 :&: SEmpty))) "core" "add"

infixl 9 &&&

infixl 9 |||
