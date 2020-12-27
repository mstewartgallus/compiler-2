{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module Ccc.Hom (fold, Closed (..), Hom) where

import Control.Category
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
  Var :: x a b -> Hom x a b

  Id :: Hom x a a
  (:.:) :: Hom x b c -> Hom x a b -> Hom x a c

  UnitHom :: Hom x a Unit

  WhereIs :: Hom x (a * b) c -> Hom x Unit a -> Hom x b c
  Kappa :: ST a -> (x Unit a -> Hom x b c) -> Hom x (a * b) c

  App :: Hom x b (a ~> c) -> Hom x Unit a -> Hom x b c
  Zeta :: ST a -> (x Unit a -> Hom x b c) -> Hom x b (a ~> c)

  U64 :: Word64 -> Hom x Unit U64
  Constant :: Lam.ST a -> String -> String -> Hom x Unit (AsObject a)
  CccIntrinsic :: Intrinsic a b -> Hom x a b

instance Category (Hom x) where
  id = Id
  Id . f = f
  f . Id = f
  f . g = f :.: g

instance Ccc (Hom x) where
  unit = UnitHom

  whereIs = WhereIs
  kappa t f = Kappa t (f . Var)

  app = App
  zeta t f = Zeta t (f . Var)

  u64 = U64
  constant = Constant
  cccIntrinsic = CccIntrinsic

instance PrettyProgram (Closed a b) where
  prettyProgram x = evalState (view (fold x)) 0

fold :: Ccc hom => Closed a b -> hom a b
fold (Closed x) = go x

go :: Ccc hom => Hom hom a b -> hom a b
go x = case x of
  Var v -> v

  Id -> id
  f :.: g -> go f . go g

  UnitHom -> unit

  WhereIs f x -> whereIs (go f) (go x)
  Kappa t f -> kappa t (\x -> go (f x))

  App f x -> app (go f) (go x)
  Zeta t f -> zeta t (\x -> go (f x))

  U64 n -> u64 n
  CccIntrinsic x -> cccIntrinsic x
  Constant t pkg name -> constant t pkg name

newtype View (a :: T) (b :: T) = V { view :: State Int (Doc Style) }
instance Category View where
  id = V $ pure $ keyword (pretty "id")
  f . g = V $ do
    f' <- view f
    g' <- view g
    pure $ parens $ sep [f', keyword $ pretty "∘", g']

instance Ccc View where
  unit = V $ pure $ keyword $ pretty "unit"

  whereIs f x = V $ pure (\f' x' -> brackets $ sep [f', x']) <*> view f <*> view x
  kappa t f = V $ do
    v <- fresh
    body <- view (f (V $ pure v))
    pure $ parens $ sep [keyword $ pretty "κ", v, keyword $ pretty ":", pretty t, keyword $ pretty "⇒", body]

  app f x = V $ pure (\f' x' -> parens $ sep [f', x']) <*> view f <*> view x
  zeta t f = V $ do
    v <- fresh
    body <- view (f (V $ pure v))
    pure $ parens $ sep [keyword $ pretty "ζ" , v, keyword $ pretty ":", pretty t, keyword $ pretty "⇒", body]

  u64 n = V $ pure (pretty n)
  constant _ pkg name = V $ pure $ pretty (pkg ++ "/" ++ name)
  cccIntrinsic x = V $ pure $ pretty (show x)

fresh :: State Int (Doc Style)
fresh = do
  n <- get
  put (n + 1)
  pure $ variable (pretty "v" <> pretty n)
