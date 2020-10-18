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
  pop :: stack (a & (b & c)) ((a * b) & c)
  push :: stack ((a * b) & c) (a & (b & c))

  curry :: stack (a & env) b -> stack env (a ~> b)
  uncurry :: stack env (a ~> b) -> stack (a & env) b

class Category code => Code code where
  unit :: code x Unit
  (&&&) :: code env a -> code env b -> code env (a * b)
  first :: code (a * b) a
  second :: code (a * b) b

  absurd :: code Void x
  (|||) :: code a c -> code b c -> code (a + b) c
  left :: code a (a + b)
  right :: code b (a + b)

class (Stack stack, Code code) => Cbpv stack code | stack -> code, code -> stack where
  return :: code env a -> stack (F env) (F a)

  thunk :: stack (F x) y -> code x (U y)
  force :: code x (U y) -> stack (F x) y

  letTo :: stack x (F a) -> (code Unit a -> stack x c) -> stack x c
  be :: code x a -> (code Unit a -> code x c) -> code x c

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

infixl 9 &&&

infixl 9 |||
