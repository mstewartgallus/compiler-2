{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module AsScheme (toScheme) where

import Cbpv.Sort
import qualified Ccc as Ccc
import qualified Ccc.Type as Ccc
import Control.Monad.State hiding (lift)
import Data.Kind
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text.Prettyprint.Doc
import Data.Typeable ((:~:) (..))
import Data.Word
import qualified Lam.Type as Lam
import Pointless
import Pointless.Hom
import Pretty
import Prelude hiding (id, (.))

toScheme :: Hom (U (F Unit)) (U (F U64)) -> Doc Style
toScheme x = case fold x of
  C y ->
    pretty rt
      <> hardline
      <> evalState (val (y (ThunkVal (PushAct UnitVal)))) 0

rt :: String
rt =
  "(define (add tple) (+ (car tple) (cdr tple)))"
    <> "(define (mul tple) (* (car tple) (cdr tple)))"

data Val x y a where
  VarVal :: x a -> Val x y a
  UnitVal :: Val x y Unit
  FstVal :: Val x y (a * b) -> Val x y a
  SndVal :: Val x y (a * b) -> Val x y b
  FanoutVal :: Val x y a -> Val x y b -> Val x y (a * b)
  LetVal :: (Val x y a -> Val x y b) -> Val x y a -> Val x y b
  ThunkVal :: (Act x y Empty -> Act x y b) -> Val x y (U b)
  U64Val :: Word64 -> Val x y U64
  IntrinsicVal :: Intrinsic a b -> Val x y a -> Val x y b

data Act x y a where
  VarAct :: y a -> Act x y a
  EmptyAct :: Act x y Empty
  DropAct :: Act x y (a & b) -> Act x y b
  PushAct :: Val x y a -> Act x y b -> Act x y (a & b)
  PassAct :: Act x y (a ~> c) -> Val x y a -> Act x y c
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
  FstVal x -> do
    x' <- val x
    pure $ parens $ sep [pretty "car", x']
  SndVal x -> do
    x' <- val x
    pure $ parens $ sep [pretty "cdr", x']
  LetVal f x -> do
    x' <- val x
    v <- fresh
    body <- val (f (VarVal (V v)))
    pure $
      parens $
        dent $
          vsep
            [ sep [pretty "let", parens (brackets $ sep [v, x'])],
              body
            ]
  ThunkVal f -> do
    body <- act (f EmptyAct)
    pure $ parens $ dent $ vsep [pretty "delay", body]
  FanoutVal x y -> do
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
  DropAct x -> do
    x' <- act x
    pure $ parens $ sep [pretty "cdr", x']
  PushAct h t -> do
    h' <- val h
    t' <- act t
    pure $ parens $ sep [pretty "cons", h', t']
  PassAct f x -> do
    f' <- act f
    x' <- val x
    pure $ parens $ sep [f', x']
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
  fst = C FstVal
  snd = C SndVal
  C x &&& C y = C $ \env -> FanoutVal (x env) (y env)

instance Stack (Prog x y)

instance Pointless (Prog x y) (Prog x y) where
  drop = K $ \x -> DropAct x
  thunk (K f) = C $ \env ->
    LetVal
      ( \env' ->
          ThunkVal (\t -> f (PushAct env' t))
      )
      env

  pass (K f) (C x) = K $ \env -> PassAct (f env) (x UnitVal)
  push (C x) = K $ \env -> PushAct (x UnitVal) env

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
