{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cbpv (Category (..), Stack (..), Code (..), Cbpv (..), Intrinsic (..)) where

import Cbpv.Sort
import qualified Ccc as Ccc
import qualified Ccc.Type as Ccc
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
class Category hom where
  id :: hom a a
  (.) :: hom b c -> hom a b -> hom a c

class Category stack => Stack (stack :: Algebra -> Algebra -> Type)

class Category code => Code code where
  unit :: code x Unit
  (&&&) :: code x a -> code x b -> code x (a * b)
  fst :: code (a * b) a
  snd :: code (a * b) b

class (Stack stack, Code code) => Cbpv stack code | stack -> code, code -> stack where
  -- It's pretty obvious this should be generalized but idk precisely how
  thunk :: SSet a -> (code Unit a -> stack Empty c) -> code a (U c)
  force :: code Unit (U a) -> stack Empty a

  pop :: SSet a -> (code Unit a -> stack b c) -> stack (a & b) c
  lift :: code Unit a -> stack b (a & b)

  zeta :: SSet a -> (code Unit a -> stack b c) -> stack b (a ~> c)
  pass :: code Unit a -> stack (a ~> b) b

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
