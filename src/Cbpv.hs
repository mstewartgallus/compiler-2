{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cbpv (Stack (..), Code (..), Cbpv (..), Intrinsic (..)) where

import Cbpv.Sort
import qualified Ccc as Ccc
import qualified Ccc.Type as Ccc
import Control.Category
import Data.Kind
import Data.Word (Word64)
import qualified Lam.Type as Lam
import Prelude hiding (id, (.))

-- |
-- As opposed to the usual monadic interface call by push value is based
-- around adjoint functors on two different categories.
--
-- There is a different formulation using oblique morphisms and an
-- indexed category instead of using the asymmetric tensor but was
-- difficult to work with.
--
-- Paul Blain Levy. "Call-by-Push-Value: A Subsuming Paradigm".
class Category stack => Stack (stack :: Algebra -> Algebra -> Type)

class Category code => Code code where
  unit :: code x Unit

  kappa :: SSet a -> (code Unit a -> code b c) -> code (a * b) c
  whereIsK :: code (a * b) c -> code Unit a -> code b c

class (Stack stack, Code code) => Cbpv stack code | stack -> code, code -> stack where
  thunk :: stack (F x) y -> code x (U y)
  force :: code x (U y) -> stack (F x) y

  pop :: SSet a -> (code Unit a -> stack b c) -> stack (a & b) c
  push :: code Unit a -> stack b (a & b)

  -- | fixme.. deprecate push ?
  whereIs :: stack (a & b) c -> code Unit a -> stack b c
  whereIs f x = f . push x

  zeta :: SSet a -> (code Unit a -> stack b c) -> stack b (a ~> c)
  pass :: code Unit a -> stack (a ~> b) b

  -- | fixme.. deprecate pass ?
  app :: stack b (a ~> c) -> code Unit a -> stack b c
  app f x = pass x . f

  u64 :: Word64 -> code Unit U64

  constant :: Lam.ST a -> String -> String -> stack (F Unit) (AsAlgebra (Ccc.AsObject a))
  cccIntrinsic :: Ccc.Intrinsic a b -> code (U (AsAlgebra a)) (U (AsAlgebra b))
  cbpvIntrinsic :: Intrinsic a b -> code a b

  add :: code (U64 * U64) U64
  add = cbpvIntrinsic AddIntrinsic

data Intrinsic a b where
  AddIntrinsic :: Intrinsic (U64 * U64) U64

instance Show (Intrinsic a b) where
  show x = case x of
    AddIntrinsic -> "$add"
