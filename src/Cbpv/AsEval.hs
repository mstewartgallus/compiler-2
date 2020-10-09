{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cbpv.AsEval (reify, Stack, Code, Action, Data) where

import Cbpv
import Control.Category
import Data.Word
import Cbpv.Sort
import qualified Lambda.Type as Lambda
import qualified Hoas.Type as Hoas
import Prelude hiding ((.), id)

reify :: Code (U (F Unit)) (U (F U64)) -> Word64
reify (C f) = case f (Thunk $ \w -> Unit :& Effect w) of
  Thunk t -> case t 0 of
    (U64 y :& _) -> y

newtype Code a b = C (Data a -> Data b)

newtype Stack a b = S (Action a -> Action b)

data family Data (a :: Set)

data instance Data (U a) = Thunk (Int -> Action a)

data instance Data Unit = Unit
data instance Data Void
data instance Data (a * b) = Pair { firstOf :: (Data a), secondOf :: (Data b) }
data instance Data (a + b) = L (Data a) | R (Data b)
newtype instance Data U64 = U64 Word64

-- | Actions are CBPVs computations but we use a different name for brevity
data family Action (a :: Algebra)
data instance Action Empty = Effect Int
data instance Action (a & b) = Data a :& Action b
infixr 9 :&
newtype instance Action (a ~> b) = Lam (Data a -> Action b)

instance Category Code where
  id = C id
  C f . C g = C (f . g)

instance Category Stack where
  id = S id
  S f . S g = S (f . g)

instance Cbpv Stack Code where
  return (C f) = S $ \(x :& w) -> f x :& w

  thunk (S f) = C $ \x -> Thunk $ \w -> f (x :& Effect w)
  force (C f) = S $ \(x :& Effect w) -> case f x of
    Thunk t -> t w

  absurd = C $ \x -> case x of {}
  C x ||| C y = C $ \env -> case env of
    L l -> x l
    R r -> y r
  left = C L
  right = C R

  unit = C $ const Unit
  C x &&& C y = C $ \env -> Pair (x env) (y env)
  first = C firstOf
  second = C secondOf

  curry (S f) = S $ \env -> Lam $ \x -> f (x :& env)
  uncurry (S f) = S $ \(x :& env) -> case f env of
     Lam y -> y x

  pop = S $ \(a :& b :& c) -> Pair a b :& c
  push = S $ \(Pair a b :& c) -> a :& b :& c

  be (C x) f = C $ \env -> case f (C $ const (x env)) of
    C y -> y env

  -- | fixme... not quite right..
  letTo (S x) f = S $ \env -> case x env of
    x' :& env' -> case f (C $ const x') of
          S y -> y env

  u64 x = C $ const (U64 x)
  constant t pkg name = case (t, pkg, name) of
     (Hoas.SU64 Hoas.:-> (Hoas.SU64 Hoas.:-> Hoas.SU64), "core", "add") -> addImpl
  -- fixme.. rename to intrinsics...
  lambdaConstant t pkg name = case (t, pkg, name) of
     (Lambda.SU64 Lambda.:->  (Lambda.SU64 Lambda.:-> Lambda.SU64), "core", "add") -> addLambdaImpl
  cbpvConstant t pkg name = case (t, pkg, name) of
     (SU64 :-> (SU64 :-> (SU64 :&: SEmpty)), "core", "add") -> addCbpvImpl

addImpl :: Stack (F Unit) (AsAlgebra (Lambda.AsObject (Hoas.U64 Hoas.~> Hoas.U64 Hoas.~> Hoas.U64)))
addImpl = S $ \(Unit :& Effect w0) ->
              Lam $ \(Thunk x) -> Lam $ \(Thunk y) -> case x w0 of
                 U64 x' :& Effect w1 -> case y w1 of
                   U64 y' :& Effect w2 -> U64 (x' + y') :& Effect w2

addLambdaImpl :: Stack (F Unit) (AsAlgebra (Lambda.U64 Lambda.~> (Lambda.U64 Lambda.~> Lambda.U64)))
addLambdaImpl = addImpl

addCbpvImpl :: Stack (F Unit) (U64 ~> (U64 ~> F U64))
addCbpvImpl = S $ \(Unit :& Effect w0) ->
              Lam $ \(U64 x) ->
              Lam $ \(U64 y) ->
                   U64 (x + y) :& Effect w0
