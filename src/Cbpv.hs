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
  id :: KnownSort a => hom a a
  (.) :: (KnownSort a, KnownSort b, KnownSort c) => hom b c -> hom a b -> hom a c

class Category stack => Stack (stack :: Algebra -> Algebra -> Type)

class Category code => Code code where
  unit :: KnownSort a => code a Unit

  fst :: (KnownSort a, KnownSort b) => code (a * b) a
  fst = kappa (\x -> x . unit)

  snd :: (KnownSort a, KnownSort b) => code (a * b) b
  snd = kappa (\_ -> id)

  kappa :: (KnownSort a, KnownSort b, KnownSort c) => (code Unit a -> code b c) -> code (a * b) c
  lift :: (KnownSort a, KnownSort b, KnownSort c) => code (a * b) c -> code Unit a -> code b c

class (Stack stack, Code code) => Cbpv stack code | stack -> code, code -> stack where
  -- It's pretty obvious this should be generalized but idk precisely how
  thunk :: (KnownSort a, KnownSort c) => (code Unit a -> stack Empty c) -> code a (U c)
  force :: KnownSort a => code Unit (U a) -> stack Empty a

  pop :: (KnownSort a, KnownSort b, KnownSort c) => (code Unit a -> stack b c) -> stack (a & b) c
  push :: (KnownSort a, KnownSort b, KnownSort c) => stack (a & b) c -> code Unit a -> stack b c

  zeta :: (KnownSort a, KnownSort b, KnownSort c) => (code Unit a -> stack b c) -> stack b (a ~> c)
  pass :: (KnownSort a, KnownSort b, KnownSort c) => stack b (a ~> c) -> code Unit a -> stack b c

  u64 :: Word64 -> code Unit U64

  constant :: Lam.KnownT a => String -> String -> stack (F Unit) (AsAlgebra (Ccc.AsObject a))
  cccIntrinsic :: (Ccc.KnownT a, Ccc.KnownT b) => Ccc.Intrinsic a b -> stack (AsAlgebra a) (AsAlgebra b)
  cbpvIntrinsic :: (KnownSort a, KnownSort b) => Intrinsic a b -> code a b

  add :: code (U64 * U64) U64
  add = cbpvIntrinsic AddIntrinsic

data Intrinsic a b where
  AddIntrinsic :: Intrinsic (U64 * U64) U64

instance Show (Intrinsic a b) where
  show x = case x of
    AddIntrinsic -> "$add"
