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
import Control.Category
import Control.Monad.State hiding (lift)
import Cbpv.Sort
import Data.Word
import Data.Kind
import Prelude hiding ((.), id)

newtype Closed (a :: Sort t) (b :: Sort t) = Closed (forall x. Hom x a b)

fold :: Cbpv c d => Closed a b -> d a b
fold (Closed x) = goC x

goC :: Cbpv c d => Hom d a b -> d a b
goC x = case x of
  Var v -> v

  Id -> id
  f :.: g -> goC f . goC g

  Thunk f -> thunk (goK f)

  UnitHom -> unit

  WhereIsK f x -> whereIsK (goC f) (goC x)
  Kappa t f -> kappa t (\x -> goC (f x))

  U64 n -> u64 n
  CccIntrinsic x -> cccIntrinsic x
  CbpvIntrinsic x -> cbpvIntrinsic x

goK :: Cbpv c d => Hom d a b -> c a b
goK x = case x of
  Id -> id
  f :.: g -> goK f . goK g

  Force f -> force (goC f)

  WhereIs f x -> whereIs (goK f) (goC x)
  Pop t f -> pop t (\x -> goK (f x))

  App f x -> app (goK f) (goC x)
  Zeta t f -> zeta t (\x -> goK (f x))

  Constant t pkg name -> constant t pkg name

data Hom (x :: Set -> Set -> Type) (a :: Sort t) (b :: Sort t) where
  Var :: x a b -> Hom x a b

  Id :: Hom x a a
  (:.:) :: Hom x b c -> Hom x a b -> Hom x a c

  Thunk :: Hom x (F a) b -> Hom x a (U b)
  Force :: Hom x a (U b) -> Hom x (F a) b

  UnitHom :: Hom x a Unit

  WhereIsK :: Hom x (a * b) c -> Hom x Unit a -> Hom x b c
  Kappa :: SSet a -> (x Unit a -> Hom x b c) -> Hom x (a * b) c

  WhereIs :: Hom x (a & b) c -> Hom x Unit a -> Hom x b c
  Pop :: SSet a -> (x Unit a -> Hom x b c) -> Hom x (a & b) c

  App :: Hom x c (a ~> b) -> Hom x Unit a -> Hom x c b
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

  whereIsK = WhereIsK
  kappa t f = Kappa t (f . Var)

instance Stack (Hom x) where

instance Cbpv (Hom x) (Hom x) where
  thunk = Thunk
  force = Force

  whereIs = WhereIs
  pop t f = Pop t (f . Var)

  app = App
  zeta t f = Zeta t (f . Var)

  u64 = U64
  constant = Constant
  cccIntrinsic = CccIntrinsic
  cbpvIntrinsic = CbpvIntrinsic

-- shit!
instance Show (Closed @SetTag a b) where
  show x = evalState (view (fold x)) 0

newtype View (a :: Sort t) (b :: Sort t) = V { view :: State Int String }

instance Category View where
  id = V $ pure "id"
  f . g = V $ do
    f' <- view f
    g' <- view g
    pure $ "(" ++ f' ++ " ∘ " ++ g' ++ ")"

instance Code View where

  unit = V $ pure "unit"

  whereIsK f x = V $ pure (\f' x' -> "<" ++ f' ++ " " ++ x' ++ ")") <*> view f <*> view x
  kappa t f = V $ do
    v <- fresh
    body <- view (f (V $ pure v))
    pure $ "(κ " ++ v ++ ": " ++ show t ++ ". " ++ body ++ ")"

instance Stack View where

instance Cbpv View View where
  thunk x = V $ pure (\x' -> "(thunk " ++ x' ++ ")") <*> view x
  force x = V $ pure (\x' -> "(force " ++ x' ++ ")") <*> view x

  whereIs f x = V $ pure (\f' x' -> "<" ++ f' ++ " " ++ x' ++ ">") <*> view f <*> view x
  pop t f = V $ do
    v <- fresh
    body <- view (f (V $ pure v))
    pure $ "(pop " ++ v ++ ": " ++ show t ++ ". " ++ body ++ ")"

  app f x = V $ pure (\f' x' -> "(" ++ f' ++ " " ++ x' ++ ")") <*> view f <*> view x
  zeta t f = V $ do
    v <- fresh
    body <- view (f (V $ pure v))
    pure $ "(ζ " ++ v ++ ": " ++ show t ++ ". " ++ body ++ ")"

  u64 n = V $ pure (show n)

  constant _ pkg name = V $ pure (pkg ++ "/" ++ name)
  cccIntrinsic x = V $ pure (show x)
  cbpvIntrinsic x = V $ pure (show x)

fresh :: State Int String
fresh = do
  n <- get
  put (n + 1)
  pure ("v" ++ show n)
