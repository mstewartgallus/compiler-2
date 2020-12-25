{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.Hom (abstract, Closed (..), Hom (..)) where

import Cbpv
import qualified Lam.Type as Lam
import qualified Ccc
import qualified Ccc.Type as Ccc
import Control.Category
import Control.Monad.State hiding (lift)
import Cbpv.Sort
import Data.Word
import Data.Kind
import Prelude hiding ((.), id)

newtype Closed a b = Closed (forall x. Hom x a b)

abstract :: Cbpv c d => Closed a b -> d a b
abstract (Closed x) = goC x

goC :: Cbpv c d => Hom d a b -> d a b
goC x = case x of
  Var v -> v

  Id -> id
  f :.: g -> goC f . goC g

  Thunk f -> thunk (goK f)

  UnitHom -> unit

  Lift x -> lift (goC x)
  Kappa t f -> kappa t (\x -> goC (f x))

  U64 n -> u64 n
  CccIntrinsic x -> cccIntrinsic x
  CbpvIntrinsic x -> cbpvIntrinsic x

goK :: Cbpv c d => Hom d a b -> c a b
goK x = case x of
  Id -> id
  f :.: g -> goK f . goK g

  Force f -> force (goC f)

  Push x -> push (goC x)
  Pop t f -> pop t (\x -> goK (f x))

  Pass x -> pass (goC x)
  Zeta t f -> zeta t (\x -> goK (f x))

  Constant t pkg name -> constant t pkg name

data Hom (x :: Set -> Set -> Type) (a :: Sort t) (b :: Sort t) where
  Var :: x a b -> Hom x a b

  Id :: Hom x a a
  (:.:) :: Hom x b c -> Hom x a b -> Hom x a c

  Thunk :: Hom x (F a) b -> Hom x a (U b)
  Force :: Hom x a (U b) -> Hom x (F a) b

  UnitHom :: Hom x a Unit

  Lift :: Hom x Unit a -> Hom x b (a * b)
  Kappa :: SSet a -> (x Unit a -> Hom x b c) -> Hom x (a * b) c

  Push :: Hom x Unit a -> Hom x b (a & b)
  Pop :: SSet a -> (x Unit a -> Hom x b c) -> Hom x (a & b) c

  Pass :: Hom x Unit a -> Hom x (a ~> b) b
  Zeta :: SSet a -> (x Unit a -> Hom x b c) -> Hom x b (a ~> c)

  U64 :: Word64 -> Hom x Unit U64

  Constant :: Lam.ST a -> String -> String -> Hom x (F Unit) (AsAlgebra (Ccc.AsObject a))
  CccIntrinsic :: Ccc.Intrinsic a b -> Hom x (U (AsAlgebra a)) (U (AsAlgebra b))
  CbpvIntrinsic :: Intrinsic a b -> Hom x a b

instance Category (Hom x) where
  id = Id
  (.) = (:.:)

instance Code (Hom x) where
  unit = UnitHom

  lift = Lift
  kappa t f = Kappa t (f . Var)

instance Stack (Hom x) where

instance Cbpv (Hom x) (Hom x) where
  thunk = Thunk
  force = Force

  push = Push
  pop t f = Pop t (f . Var)

  pass = Pass
  zeta t f = Zeta t (f . Var)

  u64 = U64
  constant = Constant
  cccIntrinsic = CccIntrinsic
  cbpvIntrinsic = CbpvIntrinsic

instance Show (Closed a b) where
  show (Closed x) = evalState (view x) 0

newtype View (a :: Sort t) (b :: Sort t) = V String

view :: Hom View a b -> State Int String
view x = case x of
  Var (V x) -> pure x

  Id -> pure "id"
  f :.: g -> do
    f' <- view f
    g' <- view g
    pure $ "(" ++ f' ++ " ∘ " ++ g' ++ ")"

  Thunk x -> pure (\x' -> "(thunk " ++ x' ++ ")") <*> view x
  Force x -> pure (\x' -> "(force " ++ x' ++ ")") <*> view x

  UnitHom -> pure "unit"

  Lift x -> pure (\x' -> "(lift " ++ x' ++ ")") <*> view x
  Kappa t f -> do
    v <- fresh
    body <- view (f (V v))
    pure $ "(κ " ++ v ++ ": " ++ "?" ++ ". " ++ body ++ ")"

  Push x -> pure (\x' -> "(push " ++ x' ++ ")") <*> view x
  Pop t f -> do
    v <- fresh
    body <- view (f (V v))
    pure $ "(pop " ++ v ++ ": " ++ "?" ++ ". " ++ body ++ ")"


  Pass x -> pure (\x' -> "(pass " ++ x' ++ ")") <*> view x
  Zeta t f -> do
    v <- fresh
    body <- view (f (V v))
    pure $ "(ζ " ++ v ++ ": " ++ "?" ++ ". " ++ body ++ ")"

  U64 n -> pure (show n)

  Constant _ pkg name -> pure (pkg ++ "/" ++ name)
  CccIntrinsic x -> pure (show x)
  CbpvIntrinsic x -> pure (show x)

fresh :: State Int String
fresh = do
  n <- get
  put (n + 1)
  pure ("v" ++ show n)
