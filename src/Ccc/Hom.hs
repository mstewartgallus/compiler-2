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
import Pretty
import Control.Monad.State hiding (lift)
import Prelude hiding (id, (.))
import qualified Lam.Type as Lam
import Data.Text.Prettyprint.Doc

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

instance PrettyProgram (Closed a b) where
  prettyProgram x = evalState (view (fold x) 0) 0

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

appPrec :: Int
appPrec = 10

kappaPrec :: Int
kappaPrec = 2

zetaPrec :: Int
zetaPrec = 5

composePrec :: Int
composePrec = 9

paren :: Bool -> Doc Style -> Doc Style
paren x y = if x then parens y else y

newtype View (a :: T) (b :: T) = V { view :: Int -> State Int (Doc Style) }

instance Ccc View where
  id = V $ \_ -> pure $ keyword (pretty "id")
  f . g = V $ \p -> do
    f' <- view f (composePrec + 1)
    g' <- view g (composePrec + 1)
    pure $ paren (p > composePrec) $ sep [f', keyword $ pretty "∘", g']

  unit = V $ \_ -> pure $ keyword $ pretty "!"

  lift x = V $ \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "lift", x']) <*> view x (appPrec + 1)
  kappa = kappa' inferT

  pass x = V $ \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "pass", x']) <*> view x (appPrec + 1)
  zeta = zeta' inferT

  u64 n = V $ \_ -> pure (pretty n)
  constant pkg name = V $ \_ -> pure $ pretty (pkg ++ "/" ++ name)
  cccIntrinsic x = V $ \_ -> pure $ pretty (show x)

kappa' :: ST a -> (View Unit a -> View b c) -> View (a * b) c
kappa' t f = V $ \p -> do
    v <- fresh
    body <- view (f (V $ \_ -> pure v)) (kappaPrec + 1)
    pure $ paren (p > kappaPrec) $ sep [keyword $ pretty "κ", v, keyword $ pretty ":", pretty t, keyword $ pretty "⇒", body]

zeta' :: ST a -> (View Unit a -> View b c) -> View b (a ~> c)
zeta' t f = V $ \p -> do
    v <- fresh
    body <- view (f (V $ \_ -> pure v)) (zetaPrec + 1)
    pure $ paren (p > zetaPrec) $ sep [keyword $ pretty "ζ", v, keyword $ pretty ":", pretty t, keyword $ pretty "⇒", body]

fresh :: State Int (Doc Style)
fresh = do
  n <- get
  put (n + 1)
  pure $ variable (pretty "v" <> pretty n)
