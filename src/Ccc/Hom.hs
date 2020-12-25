{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module Ccc.Hom (fold, Closed (..), Hom (..)) where

import Control.Category
import Data.Word
import Ccc.HasExp hiding ((<*>))
import Ccc
import Ccc.HasUnit
import Ccc.HasProduct
import Ccc.Type
import Control.Monad.State hiding (lift)
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

instance Show (Closed a b) where
  show (Closed x) = evalState (view x) 0

fold :: Ccc hom => Closed a b -> hom a b
fold (Closed x) = go x

go :: Ccc hom => Hom hom a b -> hom a b
go x = case x of
  Var v -> v

  Id -> id
  f :.: g -> go f . go g

  UnitHom -> unit

  Lift x -> lift (go x)
  Kappa t f -> kappa t (\x -> go (f x))

  Pass x -> pass (go x)
  Zeta t f -> zeta t (\x -> go (f x))

  U64 n -> u64 n
  CccIntrinsic x -> cccIntrinsic x
  Constant t pkg name -> constant t pkg name

newtype View (a :: T) (b :: T) = V String

view :: Hom View a b -> State Int String
view x = case x of
  Var (V x) -> pure x

  Id -> pure "id"
  f :.: g -> do
    f' <- view f
    g' <- view g
    pure $ "(" ++ f' ++ " ∘ " ++ g' ++ ")"

  UnitHom -> pure "unit"

  Lift x -> pure (\x' -> "(lift " ++ x' ++ ")") <*> view x
  Kappa t f -> do
    v <- fresh
    body <- view (f (V v))
    pure $ "(κ " ++ v ++ ": " ++ show t ++ ". " ++ body ++ ")"

  Pass x -> pure (\x' -> "(pass " ++ x' ++ ")") <*> view x
  Zeta t f -> do
    v <- fresh
    body <- view (f (V v))
    pure $ "(ζ " ++ v ++ ": " ++ show t ++ ". " ++ body ++ ")"

  U64 n -> pure (show n)

  Constant _ pkg name -> pure (pkg ++ "/" ++ name)
  CccIntrinsic x -> pure (show x)

fresh :: State Int String
fresh = do
  n <- get
  put (n + 1)
  pure ("v" ++ show n)
