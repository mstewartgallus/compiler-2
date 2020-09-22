{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Lambda.AsOptimized (Expr, optimize) where

import Control.Category
import Lambda
import Lambda.HasExp
import Lambda.HasProduct
import Lambda.HasSum
import Lambda.Type
import Prelude hiding ((.), id, curry, uncurry, Either (..))

-- | The optimizer is based off the idea of normalization by
-- evaluation. Next this should really be moved back to the term level
-- representation
optimize :: Category k => Expr k a b -> k a b
optimize (E x) = compile x

newtype Expr k a b = E (forall env. Value k env a -> Value k env b)

data Value k env a where
  StuckValue :: Category k => k a b -> Value k env a -> Value k env b
  EnvValue :: Category k => Value k env env

  FnValue :: HasExp k => Value k env a -> (forall x. Value k x (b * a) -> Value k x c) -> Value k env (b ~> c)

  CoinValue :: HasProduct k => Value k env Unit
  PairValue :: HasProduct k => Value k env a -> Value k env b -> Value k env (a * b)

  LeftValue :: HasSum k => Value k env a -> Value k env (a + b)
  RightValue :: HasSum k => Value k env b -> Value k env (a + b)

toExpr :: Category k => Value k env result -> k env result
toExpr expr = case expr of
  StuckValue hom x -> hom . toExpr x
  EnvValue -> id

  CoinValue -> unit
  PairValue f g -> toExpr f &&& toExpr g

  LeftValue x -> left . toExpr x
  RightValue x -> right . toExpr x

  FnValue env f -> curry f' . toExpr env where
    f' = compile f

compile :: Category k => (forall env. Value k env a -> Value k env b) -> k a b
compile f = toExpr (f EnvValue)

instance Category k => Category (Expr k) where
  id = E id
  E f . E g = E (f . g)

instance HasProduct k => HasProduct (Expr k) where
  unit = E (const CoinValue)
  E f &&& E g = E $ \x -> PairValue (f x) (g x)
  first = E $ \x -> case x of
    PairValue l _ -> l
    _ -> StuckValue first x
  second = E $ \x -> case x of
    PairValue _ r -> r
    _ -> StuckValue second x

instance HasSum k => HasSum (Expr k) where
  absurd = E (StuckValue absurd)
  E f ||| E g = E $ \x -> case x of
    LeftValue l -> f l
    RightValue r -> g r
    _ -> StuckValue (compile f ||| compile g) x
  left = E LeftValue
  right = E RightValue

instance HasExp k => HasExp (Expr k) where
  curry (E f) = E (\x -> FnValue x f)
  uncurry f = E (doUncurry f)

instance Lambda k => Lambda (Expr k) where
  u64 x = E (StuckValue $ u64 x)
  add = E (StuckValue add)

doUncurry :: HasExp k => Expr k a (b ~> c) -> Value k env (b * a) -> Value k env c
doUncurry (E f) x = let
  stuck = StuckValue (uncurry (compile f)) x
  in case x of
  PairValue b a -> case f a of
    FnValue env ep -> ep (PairValue b env)
    _ -> stuck
  _ -> stuck
