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
      <> evalState (val (y (ThunkVal (\_ -> PushAct UnitVal) UnitVal))) 0

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
  ThunkVal :: (Val x y c -> Act x y a -> Act x y b) -> Val x y c -> Val x y (a ~. b)
  U64Val :: Word64 -> Val x y U64
  IntrinsicVal :: Intrinsic a b -> Val x y a -> Val x y b

data Act x y a where
  VarAct :: y a -> Act x y a
  EmptyAct :: Act x y Empty
  DropAct :: Act x y (a & b) -> Act x y b
  ForceAct :: Val x y (a ~. b) -> Act x y a -> Act x y b
  PassAct :: Val x y a -> Act x y (a ~> b) -> Act x y b
  PushAct :: Val x y a -> Act x y b -> Act x y (a & b)
  PopAct :: (Val x y a -> Act x y b -> Act x y c) -> Act x y (a & b) -> Act x y c
  CallAct :: Lam.ST a -> String -> String -> Act x y Empty -> Act x y (AsAlgebra (Ccc.AsObject a))

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
  ThunkVal f x -> do
    x' <- val x
    k <- fresh
    body <- act (f (VarVal (V k)) (VarAct (V $ pretty "'()")))
    pure $
      parens $
        dent $
          vsep
            [ sep [pretty "let", parens (brackets $ sep [k, x'])],
              parens $ dent $ vsep [pretty "delay", body]
            ]
  FanoutVal x y -> do
    x' <- val x
    y' <- val y
    pure $ parens $ sep [pretty "cons", x', y']
  IntrinsicVal intrins (FanoutVal x y) -> do
    x' <- val x
    y' <- val y
    case intrins of
      AddIntrinsic -> pure $ parens $ sep [pretty "+", x', y']
      MulIntrinsic -> pure $ parens $ sep [pretty "*", x', y']
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
    v <- fresh
    pure $
      parens $
        dent $
          vsep
            [ sep [pretty "let", parens (brackets $ sep [v, x'])],
              parens $ sep [pretty "cdr", v]
            ]
  ForceAct f t -> do
    t' <- act t
    f' <- val f
    pure $ parens $ sep [t', parens $ sep [pretty "force", f']]
  PushAct h t -> do
    h' <- val h
    t' <- act t
    pure $ parens $ sep [t', h']
  PassAct x f -> do
    x' <- val x
    f' <- act f
    pure $ parens $ sep [f', x']
  PopAct f t -> do
    t' <- act t
    v <- fresh
    k <- fresh
    body <- act (f (VarVal (V v)) (VarAct (V k)))
    pure $
      parens $
        sep
          [ t',
            parens $ dent $ vsep [pretty "lambda", parens $ sep [v, k], body]
          ]
  CallAct _ pkg name t -> do
    t' <- act t
    pure $ parens $ sep [t', parens $ sep [pretty "call", pretty pkg, pretty name]]

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
  thunk (K f) = C (ThunkVal (\h t -> f (PushAct h t)))
  force (C f) = K $ PopAct $ \h t -> ForceAct (f h) t

  inStack = K (PushAct UnitVal)
  lmapStack (C x) = K (PopAct (\h -> PushAct (x h)))
  rmapStack (K x) = K (PopAct (\h t -> PushAct h (x t)))
  uncurry (K x) = K (PopAct (\h t -> PassAct h (x t)))

  push = K (PopAct (\h t -> PushAct (FstVal h) (PushAct (SndVal h) t)))
  pop = K (PopAct (\x -> PopAct (\y -> PushAct (FanoutVal x y))))

  u64 n = C $ \_ -> U64Val n
  constant pkg name = C (ThunkVal (\_ t -> CallAct Lam.inferT pkg name t))
  cbpvIntrinsic x = C (IntrinsicVal x)

fresh :: State Int (Doc Style)
fresh = do
  n <- get
  put (1 + n)
  pure (pretty "v" <> pretty n)

dent :: Doc a -> Doc a
dent = nest 3
