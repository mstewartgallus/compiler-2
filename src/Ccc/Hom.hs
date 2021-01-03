{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module Ccc.Hom (fold, Closed (..), Hom) where

import Data.Word
import Ccc.Type
import Ccc
import Prelude hiding (id, (.))
import qualified Lam.Type as Lam

newtype Closed a b = Closed (forall x. Hom x a b)

data Hom x a b where
  Var :: (KnownT a, KnownT b) => x a b -> Hom x a b

  Id :: KnownT a => Hom x a a
  (:.:) :: (KnownT a, KnownT b, KnownT c) => Hom x b c -> Hom x a b -> Hom x a c

  UnitHom :: KnownT a => Hom x a Unit

  Lift :: (KnownT a, KnownT b) => Hom x Unit a -> Hom x b (a * b)
  Kappa :: (KnownT a, KnownT b, KnownT c) => (x Unit a -> Hom x b c) -> Hom x (a * b) c

  Pass :: (KnownT a, KnownT b) => Hom x Unit a -> Hom x (a ~> b) b
  Zeta :: (KnownT a, KnownT b, KnownT c) => (x Unit a -> Hom x b c) -> Hom x b (a ~> c)

  U64 :: Word64 -> Hom x Unit U64
  Constant :: Lam.KnownT a => String -> String -> Hom x Unit (AsObject a)
  CccIntrinsic :: (KnownT a, KnownT b) => Intrinsic a b -> Hom x a b

instance Ccc (Hom x) where
  id = Id

  Id . f = f
  f . Id = f
  f . g = f :.: g

  unit = UnitHom

  lift = Lift
  kappa f = Kappa (\x -> f (Var x))

  pass = Pass
  zeta f = Zeta (\x -> f (Var x))

  u64 = U64
  constant = Constant
  cccIntrinsic = CccIntrinsic

fold :: Ccc hom => Closed a b -> hom a b
fold (Closed x) = go x

go :: Ccc hom => Hom hom a b -> hom a b
go x = case x of
  Var v -> v

  Id -> id
  f :.: g -> go f . go g

  UnitHom -> unit

  Lift x -> lift (go x)
  Kappa f -> kappa (\x -> go (f x))

  Pass x -> pass (go x)
  Zeta f -> zeta (\x -> go (f x))

  U64 n -> u64 n
  CccIntrinsic x -> cccIntrinsic x
  Constant pkg name -> constant pkg name
