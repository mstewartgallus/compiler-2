{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Pointless (Category (..), Stack (..), Code (..), Pointless (..), Intrinsic (..)) where

import Cbpv (Category (..), Intrinsic (..))
import Cbpv.Sort
import qualified Ccc as Ccc
import qualified Ccc.Type as Ccc
import Data.Kind
import Data.Word (Word64)
import qualified Lam.Type as Lam
import Prelude hiding (id, (.))

class Category stack => Stack (stack :: Algebra -> Algebra -> Type)

class Category code => Code code where
  unit :: KnownSort a => code a Unit

  (&&&) :: (KnownSort c, KnownSort a, KnownSort b) => code c a -> code c b -> code c (a * b)
  fst :: (KnownSort a, KnownSort b) => code (a * b) a
  snd :: (KnownSort a, KnownSort b) => code (a * b) b

class (Stack stack, Code code) => Pointless stack code | stack -> code, code -> stack where
  inStack :: KnownSort a => stack a (Unit & a)
  lmapStack :: (KnownSort a, KnownSort b, KnownSort x) => code a b -> stack (a & x) (b & x)
  rmapStack :: (KnownSort a, KnownSort b, KnownSort x) => stack a b -> stack (x & a) (x & b)

  push :: (KnownSort a, KnownSort b) => stack ((a * b) & c) (a & (b & c))
  pop :: (KnownSort a, KnownSort b) => stack (a & (b & c)) ((a * b) & c)

  thunk :: (KnownSort a, KnownSort b) => stack (F a) b -> code a (U b)
  force :: (KnownSort a, KnownSort b) => code a (U b) -> stack (F a) b

  drop :: (KnownSort a, KnownSort b) => stack (a & b) b

  uncurry :: (KnownSort a, KnownSort b, KnownSort c) => stack b (a ~> c) -> stack (a & b) c
  curry :: (KnownSort a, KnownSort b, KnownSort c) => stack (a & b) c -> stack b (a ~> c)

  u64 :: Word64 -> code Unit U64

  constant :: Lam.KnownT a => String -> String -> code Unit (U (AsAlgebra (Ccc.AsObject a)))
  cccIntrinsic :: (Ccc.KnownT a, Ccc.KnownT b) => Ccc.Intrinsic a b -> stack (AsAlgebra a) (AsAlgebra b)
  cbpvIntrinsic :: (KnownSort a, KnownSort b) => Intrinsic a b -> code a b
