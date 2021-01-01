{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.Hom (fold, Closed (..), Hom) where

import Cbpv
import qualified Lam.Type as Lam
import qualified Ccc
import qualified Ccc.Type as Ccc
import Control.Monad.State hiding (lift)
import Cbpv.Sort
import Pretty
import Data.Word
import Data.Kind
import Data.Text.Prettyprint.Doc
import Prelude hiding ((.), id, fst, snd)

newtype Closed (a :: Sort t) (b :: Sort t) = Closed (forall x. Hom x a b)

fold :: Cbpv c d => Closed a b -> d a b
fold (Closed x) = goC x

goC :: Cbpv c d => Hom d a b -> d a b
goC x = case x of
  Var v -> v

  Id -> id
  f :.: g -> goC f . goC g

  Thunk f -> thunk (\x -> goK (f x))

  UnitHom -> unit
  Fanout x y -> goC x &&& goC y
  Fst -> fst
  Snd -> snd

  U64 n -> u64 n
  CbpvIntrinsic x -> cbpvIntrinsic x

goK :: Cbpv c d => Hom d a b -> c a b
goK x = case x of
  Id -> id
  f :.: g -> goK f . goK g

  Force x -> force (goC x)

  CccIntrinsic x -> cccIntrinsic x

  Lift x -> lift (goC x)
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
  Fanout :: (KnownSort a, KnownSort b, KnownSort c) => Hom x c a -> Hom x c b -> Hom x c (a * b)
  Fst :: (KnownSort a, KnownSort b) => Hom x (a * b) a
  Snd :: (KnownSort a, KnownSort b) => Hom x (a * b) b

  Lift :: (KnownSort a, KnownSort b) => Hom x Unit a -> Hom x b (a & b)
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
  (&&&) = Fanout
  fst = Fst
  snd = Snd

instance Stack (Hom x) where

instance Cbpv (Hom x) (Hom x) where
  force = Force
  thunk f = Thunk (\x -> f (Var x))

  lift = Lift
  pop f = Pop (\x -> f (Var x))

  pass = Pass
  zeta f = Zeta (\x -> f (Var x))

  u64 = U64
  constant = Constant
  cccIntrinsic = CccIntrinsic
  cbpvIntrinsic = CbpvIntrinsic

-- shit!
instance PrettyProgram (Closed @SetTag a b) where
  prettyProgram x = evalState (view (fold x) 0) 0

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

newtype View (a :: Sort t) (b :: Sort t) = V { view :: Int -> State Int (Doc Style) }

dent :: Doc a -> Doc a
dent = nest 3

instance Category View where
  id = V $ \_ -> pure $ keyword $ pretty "id"
  f . g = V $ \p -> do
    f' <- view f (composePrec + 1)
    g' <- view g (composePrec + 1)
    pure $ paren (p > composePrec) $ vsep [f', keyword $ pretty "∘", g']

instance Code View where
  unit = V $ \_ -> pure $ keyword $ pretty "!"
  V x &&& V y = V $ \_ -> pure (\x' y' -> angles $ sep $ punctuate (keyword $ comma) [x', y']) <*> x 0 <*> y 0
  fst = V $ \_ -> pure $ keyword $ pretty "π₁"
  snd = V $ \_ -> pure $ keyword $ pretty "π₂"

instance Stack View where

instance Cbpv View View where
  force x = V $  \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "force", x']) <*> view x (appPrec + 1)
  thunk = thunk' inferSort

  lift x = V $ \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "lift", x']) <*> view x (appPrec + 1)
  pop = pop' inferSort

  pass x = V $  \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "pass", x']) <*> view x (appPrec + 1)
  zeta = zeta' inferSort

  u64 n = V $ \_ -> pure (pretty n)
  constant pkg name = V $ \_ -> pure $ pretty (pkg ++ "/" ++ name)
  cccIntrinsic x = V $ \_ -> pure $ pretty (show x)
  cbpvIntrinsic x = V $ \_ -> pure  $ pretty (show x)

thunk' :: SSet a -> (View Unit a -> View Empty c) -> View a (U c)
thunk' t f =
  V $ \p -> do
    v <- fresh
    body <- view (f (V $ \_ -> pure v)) (zetaPrec + 1)
    pure $ paren (p > zetaPrec) $ dent $ vsep [
      sep [keyword $ pretty "thunk" , v, keyword $ pretty ":", prettyProgram t, keyword $ pretty "⇒"],
           body]

pop' :: SSet a -> (View Unit a -> View b c) -> View (a & b) c
pop' t f =
  V $ \p -> do
    v <- fresh
    body <- view (f (V $ \_ -> pure v)) (kappaPrec + 1)
    pure $ paren (p > kappaPrec) $ dent $ vsep [
      sep [keyword $ pretty "κ" , v, keyword $ pretty ":", prettyProgram t, keyword $ pretty "⇒"],
      body]

zeta' :: SSet a -> (View Unit a -> View b c) -> View b (a ~> c)
zeta' t f = V $ \p -> do
    v <- fresh
    body <- view (f (V $ \_ -> pure v)) (zetaPrec + 1)
    pure $ paren (p > zetaPrec) $ dent $ vsep [
      sep [keyword $ pretty "ζ" , v, keyword $ pretty ":", prettyProgram t, keyword $ pretty "⇒"],
      body]

fresh :: State Int (Doc Style)
fresh = do
  n <- get
  put (n + 1)
  pure $ variable (pretty "v" <> pretty n)
