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
import Pretty
import Data.Word
import Data.Kind
import Data.Text.Prettyprint.Doc
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

goK :: Pointless c d => Hom a b -> c a b
goK x = case x of
  Id -> id
  f :.: g -> goK f . goK g

  Drop -> drop
  Force x -> force (goC x)

  CccIntrinsic x -> cccIntrinsic x

  Push f x -> push (goK f) (goC x)
  Pass f x -> pass (goK f) (goC x)

  -- Pop f -> pop (\x -> goK (f x))
  -- Zeta f -> zeta (\x -> goK (f x))

  Constant pkg name -> constant pkg name

data Hom (a :: Sort t) (b :: Sort t) where
  Id :: KnownSort a => Hom  a a
  (:.:) :: (KnownSort a, KnownSort b, KnownSort c) => Hom  b c -> Hom  a b -> Hom  a c

  Thunk :: (KnownSort a, KnownSort b) => Hom  (F a) b -> Hom  a (U b)
  Force :: (KnownSort a, KnownSort b) => Hom  a (U b) -> Hom  (F a) b

  UnitHom :: KnownSort a => Hom  a Unit
  Fst :: (KnownSort a, KnownSort b) => Hom  (a * b) a
  Snd :: (KnownSort a, KnownSort b) => Hom  (a * b) b
  Fanout :: (KnownSort a, KnownSort b, KnownSort c) => Hom  c a -> Hom  c b -> Hom  c (a * b)

  Drop :: (KnownSort a, KnownSort b) => Hom (a & b) b
  Push :: (KnownSort a, KnownSort b, KnownSort c) => Hom  (a & b) c -> Hom  Unit a -> Hom  b c
  Pass :: (KnownSort a, KnownSort b, KnownSort c) => Hom  b (a ~> c) -> Hom  Unit a -> Hom  b c

  U64 :: Word64 -> Hom  Unit U64

  Constant :: Lam.KnownT a => String -> String -> Hom  (F Unit) (AsAlgebra (Ccc.AsObject a))
  CccIntrinsic :: (Ccc.KnownT a, Ccc.KnownT b) => Ccc.Intrinsic a b -> Hom  (AsAlgebra a) (AsAlgebra b)
  PointlessIntrinsic :: (KnownSort a, KnownSort b) => Intrinsic a b -> Hom  a b

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

  force = Force
  thunk = Thunk

  push = Push
  pass = Pass

  u64 = U64
  constant = Constant
  cccIntrinsic = CccIntrinsic
  cbpvIntrinsic = PointlessIntrinsic

-- shit!
instance PrettyProgram (Hom @SetTag a b) where
  prettyProgram x = view (fold x) 0

appPrec :: Int
appPrec = 10

whereIsPrec :: Int
whereIsPrec = 11

kappaPrec :: Int
kappaPrec = 2

zetaPrec :: Int
zetaPrec = 5

composePrec :: Int
composePrec = 9

paren :: Bool -> Doc Style -> Doc Style
paren x y = if x then parens y else y

newtype View (a :: Sort t) (b :: Sort t) = V { view :: Int -> Doc Style }

dent :: Doc a -> Doc a
dent = nest 3

instance Category View where
  id = V $ \_ -> keyword $ pretty "id"
  f . g = V $ \p -> let
    g' = view g (composePrec + 1)
    f' = view f (composePrec + 1)
    in paren (p > composePrec) $ vsep [g', keyword $ pretty ">>>", f']

instance Code View where
  unit = V $ \_ -> keyword $ pretty "!"
  x &&& y = V $ \p -> let
    x' = view x (appPrec + 1)
    y' = view x (appPrec + 1)
    in paren (p > appPrec) $ sep [x', keyword $ pretty ",", y']
  fst = V $ \_ -> keyword $ pretty "fst"
  snd = V $ \_ -> keyword $ pretty "snd"

instance Stack View where

instance Pointless View View where
  drop = V $ \_ -> keyword $ pretty "drop"

  force x = V $ \p -> let
    x' = view x (appPrec + 1)
    in paren (p > appPrec) $ sep [keyword $ pretty "force", x']
  thunk x = V $ \p -> let
    x' = view x (appPrec + 1)
    in paren (p > appPrec) $ sep [keyword $ pretty "thunk", x']

  push f x = V $ \p -> let
    f' = view f (appPrec + 1)
    x' = view x (appPrec + 1)
    in paren (p > appPrec) $ sep [keyword $ pretty "push", f', x']
  pass f x = V $ \p -> let
    f' = view f (appPrec + 1)
    x' = view x (appPrec + 1)
    in paren (p > appPrec) $ sep [keyword $ pretty "pass", f', x']

  u64 n = V $ \_ -> pretty n
  constant pkg name = V $ \p -> paren (p > appPrec) $ sep [keyword $ pretty "call", pretty (pkg ++ "/" ++ name)]
  cccIntrinsic x = V $ \p -> paren (p > appPrec) $ sep [keyword $ pretty "ccc", pretty $ show x]
  cbpvIntrinsic x = V $ \p -> paren (p > appPrec) $ sep [keyword $ pretty "intrinsic", pretty $ show x]
