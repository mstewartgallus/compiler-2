{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.Hom (fold, foldK, Closed (..), Hom) where

import Cbpv
import qualified Lam.Type as Lam
import qualified Ccc
import qualified Ccc.Type as Ccc
import Control.Monad.State hiding (lift)
import Cbpv.Sort
import Data.Word
import Data.Kind
import Prelude hiding ((.), id, fst, snd)

newtype Closed (a :: Sort t) (b :: Sort t) = Closed (forall x. Hom x a b)

fold :: Cbpv c d => Closed a b -> d a b
fold (Closed x) = goC x

foldK :: Cbpv c d => Closed a b -> c a b
foldK (Closed x) = goK x

goC :: Cbpv c d => Hom d a b -> d a b
goC x = case x of
  Var v -> v

  Id -> id
  f :.: g -> goC f . goC g

  Thunk f -> thunk (\x -> goK (f x))

  UnitHom -> unit
  Kappa f -> kappa (\x -> goC (f x))
  Lift x -> lift (goC x)

  U64 n -> u64 n
  CbpvIntrinsic x -> cbpvIntrinsic x

goK :: Cbpv c d => Hom d a b -> c a b
goK x = case x of
  Id -> id
  f :.: g -> goK f . goK g

  Force x -> force (goC x)

  CccIntrinsic x -> cccIntrinsic x

  Push x -> push(goC x)
  Pop f -> pop (\x -> goK (f x))

  Pass x -> pass (goC x)
  Zeta f -> zeta (\x -> goK (f x))

  Constant pkg name -> constant pkg name

data Hom (x :: Set -> Set -> Type) (a :: Sort t) (b :: Sort t) where
  Var :: (KnownSort a, KnownSort b) => x a b -> Hom x a b

  Id :: KnownSort a => Hom x a a
  (:.:) :: (KnownSort a, KnownSort b, KnownSort c) => Hom x b c -> Hom x a b -> Hom x a c

  Thunk :: (KnownSort a, KnownSort c) => (x Unit a -> Hom x Empty c) -> Hom x a (U c)
  Force :: KnownSort a => Hom x Unit (U a) -> Hom x Empty a

  UnitHom :: KnownSort a => Hom x a Unit

  Lift :: (KnownSort a, KnownSort b) => Hom x Unit a -> Hom x b (a * b)
  Kappa :: (KnownSort a, KnownSort b, KnownSort c) => (x Unit a -> Hom x b c) -> Hom x (a * b) c

  Push :: (KnownSort a, KnownSort b) => Hom x Unit a -> Hom x b (a & b)
  Pop :: (KnownSort a, KnownSort b, KnownSort c) => (x Unit a -> Hom x b c) -> Hom x (a & b) c

  Pass :: (KnownSort a, KnownSort b) => Hom x Unit a -> Hom x (a ~> b) b
  Zeta :: (KnownSort a, KnownSort b, KnownSort c) => (x Unit a -> Hom x b c) -> Hom x b (a ~> c)

  U64 :: Word64 -> Hom x Unit U64

  Constant :: Lam.KnownT a => String -> String -> Hom x (F Unit) (AsAlgebra (Ccc.AsObject a))
  CccIntrinsic :: (Ccc.KnownT a, Ccc.KnownT b) => Ccc.Intrinsic a b -> Hom x (AsAlgebra a) (AsAlgebra b)
  CbpvIntrinsic :: (KnownSort a, KnownSort b) => Intrinsic a b -> Hom x a b

instance Category (Hom x) where
  id = Id
  Id . f = f
  f . Id = f
  f . g = f :.: g

instance Code (Hom x) where
  unit = UnitHom
  lift = Lift
  kappa f = Kappa (\x -> f (Var x))

instance Stack (Hom x) where

instance Cbpv (Hom x) (Hom x) where
  force = Force
  thunk f = Thunk (\x -> f (Var x))

  push = Push
  pop f = Pop (\x -> f (Var x))

  pass = Pass
  zeta f = Zeta (\x -> f (Var x))

  u64 = U64
  constant = Constant
  cccIntrinsic = CccIntrinsic
  cbpvIntrinsic = CbpvIntrinsic
