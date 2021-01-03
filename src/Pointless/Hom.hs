{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Pointless.Hom (fold, foldK, Hom) where

import Pointless
import qualified Lam.Type as Lam
import qualified Ccc
import qualified Ccc.Type as Ccc
import Cbpv.Sort
import Data.Word
import Data.Kind
import Prelude hiding ((.), id, fst, snd, drop)

fold :: Pointless c d => Hom a b -> d a b
fold x = goC x

foldK :: Pointless c d => Hom a b -> c a b
foldK x = goK x

goC :: Pointless c d => Hom a b -> d a b
goC x = case x of
  Id -> id
  f :.: g -> goC f . goC g

  Thunk f -> thunk (goK f)

  UnitHom -> unit
  Fst -> fst
  Snd -> snd
  Fanout x y -> goC x &&& goC y

  U64 n -> u64 n
  PointlessIntrinsic x -> cbpvIntrinsic x
  Constant pkg name -> constant pkg name

goK :: Pointless c d => Hom a b -> c a b
goK x = case x of
  Id -> id
  f :.: g -> goK f . goK g

  Drop -> drop
  Force x -> force (goC x)

  CccIntrinsic x -> cccIntrinsic x

  Push -> push
  Pop -> pop

  InStack -> inStack

  LmapStack x -> lmapStack (goC x)
  RmapStack x -> rmapStack (goK x)

data Hom (a :: Sort t) (b :: Sort t) where
  Id :: KnownSort a => Hom a a
  (:.:) :: (KnownSort a, KnownSort b, KnownSort c) => Hom b c -> Hom a b -> Hom a c

  Thunk :: (KnownSort a, KnownSort b) => Hom (F a) b -> Hom a (U b)
  Force :: (KnownSort a, KnownSort b) => Hom a (U b) -> Hom (F a) b

  UnitHom :: KnownSort a => Hom a Unit
  Fst :: (KnownSort a, KnownSort b) => Hom (a * b) a
  Snd :: (KnownSort a, KnownSort b) => Hom (a * b) b
  Fanout :: (KnownSort a, KnownSort b, KnownSort c) => Hom c a -> Hom c b -> Hom c (a * b)

  Drop :: (KnownSort a, KnownSort b) => Hom (a & b) b
  InStack :: (KnownSort a) => Hom a (Unit & a)
  LmapStack :: (KnownSort a, KnownSort b, KnownSort x) => Hom a b -> Hom (a & x) (b & x)
  RmapStack :: (KnownSort a, KnownSort b, KnownSort x) => Hom a b -> Hom (x & a) (x & b)

  Push :: (KnownSort a, KnownSort b) => Hom ((a * b) & c) (a & b & c)
  Pop :: (KnownSort a, KnownSort b) => Hom (a & b & c) ((a * b) & c)

  Pass :: (KnownSort a, KnownSort b) => Hom Unit a -> Hom (a ~> b) b

  U64 :: Word64 -> Hom  Unit U64

  Constant :: Lam.KnownT a => String -> String -> Hom Unit (U (AsAlgebra (Ccc.AsObject a)))
  CccIntrinsic :: (Ccc.KnownT a, Ccc.KnownT b) => Ccc.Intrinsic a b -> Hom (AsAlgebra a) (AsAlgebra b)
  PointlessIntrinsic :: (KnownSort a, KnownSort b) => Intrinsic a b -> Hom a b

instance Category Hom where
  id = Id
  Id . f = f
  f . Id = f
  f . g = f :.: g

instance Code Hom where
  unit = UnitHom
  fst = Fst
  snd = Snd
  (&&&) = Fanout

instance Stack Hom where

instance Pointless Hom Hom where
  drop = Drop
  inStack = InStack

  force = Force
  thunk = Thunk

  push = Push
  pop = Pop

  lmapStack = LmapStack
  rmapStack = RmapStack

  u64 = U64
  constant = Constant
  cccIntrinsic = CccIntrinsic
  cbpvIntrinsic = PointlessIntrinsic
