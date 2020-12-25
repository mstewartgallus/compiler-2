{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module Ccc.Hom (fold, Closed (..), Hom) where

import Control.Category
import Data.Word
import Ccc.HasExp hiding ((<*>))
import Ccc.HasUnit
import Ccc.HasProduct
import Ccc.Type
import Ccc
import Control.Monad.State hiding (lift)
import Prelude hiding (id, (.))
import qualified Lam.Type as Lam

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
  (.) = (:.:)

instance HasUnit (Hom x) where
  unit = UnitHom

instance HasProduct (Hom x) where
  whereIs = WhereIs
  kappa t f = Kappa t (f . Var)

instance HasExp (Hom x) where
  app = App
  zeta t f = Zeta t (f . Var)

instance Ccc (Hom x) where
  u64 = U64
  constant = Constant
  cccIntrinsic = CccIntrinsic

instance Show (Closed a b) where
  show x = evalState (view (fold x)) 0

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

newtype View (a :: T) (b :: T) = V { view :: State Int String }
instance Category View where
  id = V $ pure "id"
  f . g = V $ do
    f' <- view f
    g' <- view g
    pure $ "(" ++ f' ++ " ∘ " ++ g' ++ ")"

instance HasUnit View where
  unit = V $ pure "unit"

instance HasProduct View where
  whereIs f x = V $ pure (\f' x' -> "(" ++ f' ++ " " ++ x' ++ ")") <*> view f <*> view x
  kappa t f = V $ do
    v <- fresh
    body <- view (f (V $ pure v))
    pure $ "(κ " ++ v ++ ": " ++ show t ++ ". " ++ body ++ ")"

instance HasExp View where
  app f x = V $ pure (\f' x' -> "<" ++ f' ++ " " ++ x' ++ ">") <*> view f <*> view x
  zeta t f = V $ do
    v <- fresh
    body <- view (f (V $ pure v))
    pure $ "(ζ " ++ v ++ ": " ++ show t ++ ". " ++ body ++ ")"

instance Ccc View where
  u64 n = V $ pure (show n)
  constant _ pkg name = V $ pure (pkg ++ "/" ++ name)
  cccIntrinsic x = V $ pure (show x)

fresh :: State Int String
fresh = do
  n <- get
  put (n + 1)
  pure ("v" ++ show n)
