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
toScheme x = case Hom.fold x of
  C y -> evalState (val (y (ThunkVal (PushAct UnitVal)))) 0

data Val x a where
  VarVal :: x a -> Val x a
  UnitVal :: Val x Unit
  ThunkVal :: Act x Empty a -> Val x (U a)
  FanoutVal :: Val x a -> Val x b -> Val x (a * b)
  U64Val :: Word64 -> Val x U64
  IntrinsicVal :: Intrinsic a b -> Val x a -> Val x b

data Act x a b where
  IdAct :: Act x a a
  ComposeAct :: Act x b c -> Act x a b -> Act x a c
  PushAct :: Val x a -> Act x b (a & b)
  PassAct :: Val x a -> Act x (a ~> b) b
  PopAct :: (Val x a -> Act x b c) -> Act x (a & b) c
  CallAct :: Lam.ST a -> String -> String -> Act x (F Unit) (AsAlgebra (Ccc.AsObject a))

data family Prog (x :: Set -> Type) (a :: Sort t) (b :: Sort t)
newtype instance Prog x (a :: Set) (b :: Set) = C (Val x a -> Val x b)
newtype instance Prog x (a :: Algebra) (b :: Algebra) = K (Act x a b)

newtype V (a :: Set) = V (Doc Style)

val :: Val V a -> State Int (Doc Style)
val x = case x of
  VarVal (V x) -> pure x
  UnitVal -> pure $ pretty "'()"
  U64Val n -> pure $ pretty n
  ThunkVal a -> do
    a' <- act a
    pure $ parens $ sep [pretty "delay", a']
  FanoutVal x y -> do
    x' <- val x
    y' <- val y
    pure $ parens $ sep [x', pretty ".", y']
  IntrinsicVal intrins arg -> do
    arg' <- val arg
    case intrins of
      AddIntrinsic -> pure $ parens $ sep [pretty "+", arg']

act :: Act V a b -> State Int (Doc Style)
act x = case x of
  IdAct -> pure $ pretty "id"
  ComposeAct f g -> do
    f' <- act f
    g' <- act g
    pure $ parens $ vsep [g', f']
  PushAct v -> do
    v' <- val v
    pure $ parens $ sep [pretty "push", v']
  PassAct v -> do
    v' <- val v
    pure $ parens $ sep [pretty "pass", v']
  PopAct f -> do
    v <- fresh
    body <- act (f (VarVal (V v)))
    pure $ parens $ dent $ vsep [sep [pretty "pop", parens v], body]
  CallAct _ pkg name -> do
    pure $ parens $ sep [pretty "call", pretty pkg, pretty name]

instance Category (Prog @SetTag x) where
  id = C (\x -> x)
  C f . C g = C $ \x -> f (g x)

instance Category (Prog @AlgebraTag x) where
  id = K IdAct
  K f . K g = K (ComposeAct f g)

instance Code (Prog x) where
  unit = C $ \_ -> UnitVal
  C x &&& C y = C $ \env -> FanoutVal (x env) (y env)

instance Stack (Prog x) where

instance Cbpv (Prog x) (Prog x) where
  thunk f = C $ \env -> case f (C $ \_ -> env) of
    K y -> ThunkVal y

  pass (C x) = K (PassAct (x UnitVal))

  lift (C x) = K (PushAct (x UnitVal))

  pop f = K $ PopAct $ \x -> case f (C $ \_ -> x) of
    K y -> y

  u64 n = C $ \_ -> U64Val n
  constant pkg name = K (CallAct Lam.inferT pkg name)
  cbpvIntrinsic x = C $ \arg -> case x of
     AddIntrinsic -> IntrinsicVal x arg

fresh :: State Int (Doc Style)
fresh = do
  n <- get
  put (1 + n)
  pure (pretty "v" <> pretty n)

dent :: Doc a -> Doc a
dent = nest 3
