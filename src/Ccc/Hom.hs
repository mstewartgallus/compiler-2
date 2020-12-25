{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module Ccc.Hom (Hom (..)) where

import Control.Category
import Data.Word
import Ccc.HasExp hiding ((<*>))
import Ccc
import Ccc.HasUnit
import Ccc.HasProduct
import Ccc.Type
import Control.Monad.State
import Prelude hiding (id, (.))
import qualified Lam.Type as Lam

newtype Closed a b = Closed (forall x. Hom x a b)

data Hom x a b where
  Var :: x a b -> Hom x a b

  Id :: Hom x a a
  (:.:) :: Hom x b c -> Hom x a b -> Hom x a c

  UnitHom :: Hom x a Unit

  Lift :: Hom x Unit a -> Hom x b (a * b)
  Kappa :: ST a -> (x Unit a -> Hom x b c) -> Hom x (a * b) c

  Pass :: Hom x Unit a -> Hom x (a ~> b) b
  Zeta :: ST a -> (x Unit a -> Hom x b c) -> Hom x b (a ~> c)

  U64 :: Word64 -> Hom x Unit U64
  Constant :: Lam.ST a -> String -> String -> Hom x Unit (AsObject a)
  CccIntrinsic :: Intrinsic a b -> Hom x a b

instance Category (Hom x) where
  id = Id
  (.) = (:.:)

instance HasUnit (Hom x) where
  unit = UnitHom

instance HasProduct (Hom x) where
  lift = Lift
  kappa t f = Kappa t (f . Var)

instance HasExp (Hom x) where
  pass = Pass
  zeta t f = Zeta t (f . Var)

instance Ccc (Hom x) where
  u64 = U64
  constant = Constant
  cccIntrinsic = CccIntrinsic
