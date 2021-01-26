{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cps (Category (..), Stack (..), Code (..), Cps (..), Intrinsic (..)) where

import Cbpv (Intrinsic (..))
import qualified Cbpv as Cbpv
import qualified Cbpv.Sort as Cbpv
import qualified Ccc as Ccc
import qualified Ccc.Type as Ccc
import Cps.Sort
import Data.Kind
import Data.Word (Word64)
import qualified Lam.Type as Lam
import Prelude hiding (id, (.))

-- |
-- A CPS-ification of call by push value.
class Category hom where
  id :: KnownSort a => hom a a
  (.) :: (KnownSort a, KnownSort b, KnownSort c) => hom b c -> hom a b -> hom a c

class Category stack => Stack (stack :: Algebra -> Algebra -> Type)

class Category code => Code code where
  unit :: KnownSort a => code a Unit

  (&&&) :: (KnownSort a, KnownSort b, KnownSort c) => code c a -> code c b -> code c (a * b)
  fst :: (KnownSort a, KnownSort b) => code (a * b) a
  snd :: (KnownSort a, KnownSort b) => code (a * b) b

class (Stack stack, Code code) => Cps stack code | stack -> code, code -> stack where
  thunk :: (KnownSort a, KnownSort b, KnownSort c) => (code Unit a -> stack b c) -> code a (b ~. c)
  force :: (KnownSort a, KnownSort b) => code Unit (b ~. a) -> stack b a

  pop :: (KnownSort a, KnownSort b, KnownSort c) => (code Unit a -> stack b c) -> stack (a & b) c
  push :: (KnownSort a, KnownSort b) => code Unit a -> stack b (a & b)

  cozeta :: (KnownSort a, KnownSort b, KnownSort c) => (code a Void -> stack c b) -> stack (c |- a) b
  copass :: (KnownSort a, KnownSort b) => code a Void -> stack b (b |- a)

  u64 :: Word64 -> code Unit U64

-- constant :: Lam.KnownT a => String -> String -> code Unit (U (AsAlgebra (Ccc.AsObject a)))
-- cccIntrinsic :: (Ccc.KnownT a, Ccc.KnownT b) => Ccc.Intrinsic a b -> stack (AsAlgebra a) (AsAlgebra b)
-- cbpvIntrinsic :: (KnownSort a, KnownSort b) => Intrinsic a b -> code a b

-- add :: code (U64 * U64) U64
-- add = cbpvIntrinsic AddIntrinsic

-- data Intrinsic a b where
--   AddIntrinsic :: Intrinsic (U64 * U64) U64
--   MulIntrinsic :: Intrinsic (U64 * U64) U64

-- instance Show (Intrinsic a b) where
--   show x = case x of
--     AddIntrinsic -> "$add"
--     MulIntrinsic -> "$mul"
