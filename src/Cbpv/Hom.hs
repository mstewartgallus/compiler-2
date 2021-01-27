{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.Hom (Closed (..), Hom) where

import Cbpv
import qualified Lam.Type as Lam
import qualified Ccc
import qualified Ccc.Type as Ccc
import Control.Monad.State hiding (lift)
import Cbpv.Sort
import Data.Word
import Data.Kind
import Prelude hiding ((.), id, fst, snd)

newtype Closed (a :: t) (b :: t) = Closed (forall x. Hom x a b)
instance Term Closed Closed where
  foldCode (Closed x) = goC x
  foldStack (Closed x) = goK x

goC :: Cbpv c d => Hom d a b -> d a b
goC x = case x of
  Var v -> v

  Id -> id
  f :.: g -> goC f . goC g

  Thunk f -> thunk (\x -> goK (f x))

  UnitHom -> unit
  Fst -> fst
  Snd -> snd
  Fanout x y -> goC x &&& goC y

  U64 n -> u64 n
  CbpvIntrinsic x -> cbpvIntrinsic x
  Constant pkg name -> constant pkg name

goK :: Cbpv c d => Hom d a b -> c a b
goK x = case x of
  Skip -> skip
  f :<<<: g -> goK f <<< goK g

  Force x -> force (goC x)

  CccIntrinsic x -> cccIntrinsic x

  Push x -> push(goC x)
  Pop f -> pop (\x -> goK (f x))

  Pass x -> pass (goC x)
  Zeta f -> zeta (\x -> goK (f x))

data Hom (x :: Set -> Set -> Type) (a :: t) (b :: t) where
  Var :: (KnownSet a, KnownSet b) => x a b -> Hom x a b

  Skip :: KnownAlgebra a => Hom x a a
  (:<<<:) :: (KnownAlgebra a, KnownAlgebra b, KnownAlgebra c) => Hom x b c -> Hom x a b -> Hom x a c

  Id :: KnownSet a => Hom x a a
  (:.:) :: (KnownSet a, KnownSet b, KnownSet c) => Hom x b c -> Hom x a b -> Hom x a c

  Thunk :: (KnownSet a, KnownAlgebra b, KnownAlgebra c) => (x Unit a -> Hom x b c) -> Hom x a (b ~. c)
  Force :: (KnownAlgebra a, KnownAlgebra b) => Hom x Unit (b ~. a) -> Hom x b a

  UnitHom :: KnownSet a => Hom x a Unit

  Fst :: (KnownSet a, KnownSet b) => Hom x (a * b) a
  Snd :: (KnownSet a, KnownSet b) => Hom x (a * b) b
  Fanout :: (KnownSet a, KnownSet b, KnownSet c) => Hom x c a -> Hom x c b -> Hom x c (a * b)

  Push :: (KnownSet a, KnownAlgebra b) => Hom x Unit a -> Hom x b (a & b)
  Pop :: (KnownSet a, KnownAlgebra b, KnownAlgebra c) => (x Unit a -> Hom x b c) -> Hom x (a & b) c

  Pass :: (KnownSet a, KnownAlgebra b) => Hom x Unit a -> Hom x (a ~> b) b
  Zeta :: (KnownSet a, KnownAlgebra b, KnownAlgebra c) => (x Unit a -> Hom x b c) -> Hom x b (a ~> c)

  U64 :: Word64 -> Hom x Unit U64

  Constant :: Lam.KnownT a => String -> String -> Hom x Unit (U (AsAlgebra (Ccc.AsObject a)))
  CccIntrinsic :: (Ccc.KnownT a, Ccc.KnownT b) => Ccc.Intrinsic a b -> Hom x (AsAlgebra a) (AsAlgebra b)
  CbpvIntrinsic :: (KnownSet a, KnownSet b) => Intrinsic a b -> Hom x a b

instance Code (Hom x) where
  id = Id
  Id . f = f
  f . Id = f
  f . g = f :.: g

  unit = UnitHom
  fst = Fst
  snd = Snd
  (&&&) = Fanout

instance Stack (Hom x) where
  skip = Skip
  Skip <<< f = f
  f <<< Skip = f
  f <<< g = f :<<<: g

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
