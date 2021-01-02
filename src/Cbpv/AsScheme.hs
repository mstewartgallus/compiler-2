{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.AsScheme (toScheme) where

import Cbpv
import qualified Cbpv.Hom as Hom
import Data.Word
import Data.Kind
import Cbpv.Sort
import qualified Ccc.Type as Ccc
import qualified Ccc as Ccc
import qualified Lam.Type as Lam
import Prelude hiding ((.), id)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable ((:~:) (..))
import Data.Text.Prettyprint.Doc
import Pretty
import Control.Monad.State hiding (lift)

toScheme :: Hom.Closed (U (F Unit)) (U (F U64)) -> Doc Style
toScheme x = toScheme' $ Hom.Closed (force (Hom.fold x . thunk (\_ -> push id unit)))

toScheme' :: Hom.Closed Empty (F U64) -> Doc Style
toScheme' x = case Hom.foldK x of
  K y -> pretty rt <>
         hardline <>
         evalState (act (y EmptyAct)) 0

rt :: String
rt =
  "(define (add tple) (+ (car tple) (cdr tple)))" <>
  "(define (mul tple) (* (car tple) (cdr tple)))"

data Val x y a where
  VarVal :: x a -> Val x y a
  UnitVal :: Val x y Unit

  LiftVal :: Val x y a -> Val x y b -> Val x y (a * b)
  KappaVal :: Val x y (a * b) -> (Val x y a -> Val x y b -> Val x y c) -> Val x y c

  ThunkVal :: Act x y a -> Val x y (U a)

  U64Val :: Word64 -> Val x y U64
  IntrinsicVal :: Intrinsic a b -> Val x y a -> Val x y b

data Act x y a where
  VarAct :: y a -> Act x y a
  EmptyAct :: Act x y Empty
  ForceAct :: Val x y (U a) -> Act x y a
  PushAct :: Val x y a -> Act x y b -> Act x y (a & b)
  PassAct :: Act x y (a ~> c) -> Val x y a -> Act x y c
  PopAct :: Act x y (a & b) -> (Val x y a -> Act x y b -> Act x y c) -> Act x y c
  CallAct :: Lam.ST a -> String -> String -> Act x y (AsAlgebra (Ccc.AsObject a))

data family Prog (x :: Set -> Type) (y :: Algebra -> Type) (a :: Sort t) (b :: Sort t)
newtype instance Prog x y (a :: Set) (b :: Set) = C (Val x y a -> Val x y b)
newtype instance Prog x y (a :: Algebra) (b :: Algebra) = K (Act x y a -> Act x y b)

newtype V (a :: Sort t) = V (Doc Style)

val :: Val V V a -> State Int (Doc Style)
val x = case x of
  VarVal (V x) -> pure x
  UnitVal -> pure $ pretty "'()"
  U64Val n -> pure $ pretty n
  ThunkVal a -> do
    a' <- act a
    pure $ parens $ dent $ vsep [pretty "delay", a']
  KappaVal x f -> do
    x' <- val x
    v <- fresh
    let h = parens $ sep [pretty "car", v]
    let t = parens $ sep [pretty "cdr", v]
    body <- val (f (VarVal (V h)) (VarVal (V t)))
    pure $ parens $ dent $ sep [pretty "let", parens $ brackets $ sep [v, x'], body]
  LiftVal x y -> do
    x' <- val x
    y' <- val y
    pure $ parens $ sep [pretty "cons", x', y']
  IntrinsicVal intrins arg -> do
    arg' <- val arg
    case intrins of
      AddIntrinsic -> pure $ parens $ sep [pretty "add", arg']
      MulIntrinsic -> pure $ parens $ sep [pretty "mul", arg']

act :: Act V V a -> State Int (Doc Style)
act x = case x of
  VarAct (V x) -> pure x
  EmptyAct -> pure $ pretty "'()"
  ForceAct x -> do
    x' <- val x
    pure $ parens $ sep [pretty "force", x']
  PushAct h t -> do
    h' <- val h
    t' <- act t
    pure $ parens $ sep [pretty "cons", h', t']
  PassAct f x -> do
    f' <- act f
    x' <- val x
    pure $ parens $ sep [f', x']
  PopAct x f -> do
    x' <- act x
    v <- fresh
    let h = parens $ sep [pretty "car", v]
    let t = parens $ sep [pretty "cdr", v]
    body <- act (f (VarVal (V h)) (VarAct (V t)))
    pure $ parens $ dent $ sep [pretty "let", parens $ brackets $ sep [v, x'], body]
  CallAct _ pkg name -> do
    pure $ parens $ sep [pretty "call", pretty pkg, pretty name]

instance Category (Prog @SetTag x y) where
  id = C (\x -> x)
  C f . C g = C $ \x -> f (g x)

instance Category (Prog @AlgebraTag x y) where
  id = K (\x -> x)
  K f . K g = K $ \x -> f (g x)

instance Code (Prog x y) where
  unit = C $ \_ -> UnitVal

  lift (C f) (C x) = C $ \env -> f (LiftVal (x UnitVal) env)
  kappa f = C $ \x -> KappaVal x $ \h t -> case f (C $ \_ -> h) of
    C y -> y t

instance Stack (Prog x y) where

instance Cbpv (Prog x y) (Prog x y) where
  force (C x) = K $ \_ -> ForceAct (x UnitVal)
  thunk f = C $ \env -> case f (C $ \_ -> env) of
    K y -> ThunkVal (y EmptyAct)

  pass (K f) (C x) = K $ \env -> PassAct (f env) (x UnitVal)
  push (K f) (C x) = K $ \env -> f (PushAct (x UnitVal) env)

  pop f = K $ \x -> PopAct x $ \h t -> case f (C $ \_ -> h) of
    K y -> y t

  u64 n = C $ \_ -> U64Val n
  constant pkg name = K $ \_ -> CallAct Lam.inferT pkg name
  cbpvIntrinsic x = C (IntrinsicVal x)

fresh :: State Int (Doc Style)
fresh = do
  n <- get
  put (1 + n)
  pure (pretty "v" <> pretty n)

dent :: Doc a -> Doc a
dent = nest 3
