{-# LANGUAGE DataKinds #-}
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
rt = "(define (add tple) + (vector-ref tple 0) (vector-ref tple 1))"

data Val x a where
  VarVal :: x a -> Val x a
  UnitVal :: Val x Unit
  FstVal :: Val x (a * b) -> Val x a
  SndVal :: Val x (a * b) -> Val x b
  ThunkVal :: Act x a -> Val x (U a)
  FanoutVal :: Val x a -> Val x b -> Val x (a * b)
  U64Val :: Word64 -> Val x U64
  IntrinsicVal :: Intrinsic a b -> Val x a -> Val x b

data Act x a where
  EmptyAct :: Act x Empty
  ForceAct :: Val x (U a) -> Act x a
  PushAct :: Act x b -> Val x a -> Act x (a & b)
  PassAct :: Act x (a ~> c) -> Val x a -> Act x c
  -- PopAct :: (Val x a -> Act x b c) -> Act x (a & b) c
  CallAct :: Lam.ST a -> String -> String -> Act x (AsAlgebra (Ccc.AsObject a))

data family Prog (x :: Set -> Type) (a :: Sort t) (b :: Sort t)
newtype instance Prog x (a :: Set) (b :: Set) = C (Val x a -> Val x b)
newtype instance Prog x (a :: Algebra) (b :: Algebra) = K (Act x a -> Act x b)

newtype V (a :: Set) = V (Doc Style)

val :: Val V a -> State Int (Doc Style)
val x = case x of
  VarVal (V x) -> pure x
  UnitVal -> pure $ pretty "'()"
  U64Val n -> pure $ pretty n
  ThunkVal a -> do
    a' <- act a
    pure $ parens $ dent $ vsep [pretty "delay", a']
  FstVal x -> do
    x' <- val x
    pure $ parens $ sep [pretty "vector-ref", x', pretty "0"]
  SndVal x -> do
    x' <- val x
    pure $ parens $ sep [pretty "vector-ref", x', pretty "1"]
  FanoutVal x y -> do
    x' <- val x
    y' <- val y
    pure $ parens $ sep [pretty "vector", x', y']
  IntrinsicVal intrins arg -> do
    arg' <- val arg
    case intrins of
      AddIntrinsic -> pure $ parens $ sep [pretty "add", arg']

act :: Act V a -> State Int (Doc Style)
act x = case x of
  EmptyAct -> pure $ pretty "(vector)"
  ForceAct x -> do
    x' <- val x
    pure $ parens $ sep [pretty "force", x']
  PushAct f x -> do
    f' <- act f
    x' <- val x
    pure $ parens $ sep [pretty "vector", f', x']
  PassAct f x -> do
    f' <- act f
    x' <- val x
    pure $ parens $ sep [f', x']
  -- PopAct f -> do
  --   v <- fresh
  --   body <- act (f (VarVal (V v)))
  --   pure $ parens $ dent $ vsep [sep [pretty "pop", parens v], body]
  CallAct _ pkg name -> do
    pure $ parens $ sep [pretty "call", pretty pkg, pretty name]

instance Category (Prog @SetTag x) where
  id = C (\x -> x)
  C f . C g = C $ \x -> f (g x)

instance Category (Prog @AlgebraTag x) where
  id = K (\x -> x)
  K f . K g = K $ \x -> f (g x)

instance Code (Prog x) where
  unit = C $ \_ -> UnitVal

  lift (C f) (C x) = C $ \env -> f (FanoutVal (x UnitVal) env)
  kappa f = C $ \x -> case f (C $ \_ -> FstVal x) of
    C y -> y (SndVal x)

instance Stack (Prog x) where

instance Cbpv (Prog x) (Prog x) where
  force (C x) = K $ \_ -> ForceAct (x UnitVal)
  thunk f = C $ \env -> case f (C $ \_ -> env) of
    K y -> ThunkVal (y EmptyAct)

  pass (K f) (C x) = K $ \env -> PassAct (f env) (x UnitVal)
  push (K f) (C x) = K $ \env -> f (PushAct env (x UnitVal))

  -- pop f = K $ PopAct $ \x -> case f (C $ \_ -> x) of
  --   K y -> y

  u64 n = C $ \_ -> U64Val n
  constant pkg name = K $ \_ -> CallAct Lam.inferT pkg name
  cbpvIntrinsic x = C $ \arg -> case x of
     AddIntrinsic -> IntrinsicVal x arg

fresh :: State Int (Doc Style)
fresh = do
  n <- get
  put (1 + n)
  pure (pretty "v" <> pretty n)

dent :: Doc a -> Doc a
dent = nest 3
