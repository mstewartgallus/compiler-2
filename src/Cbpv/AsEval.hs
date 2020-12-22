{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cbpv.AsEval (reify, Stk, Cde, Action, Data) where

import Cbpv
import Control.Category
import Data.Word
import Cbpv.Sort
import qualified Lambda.Type as Lambda
import qualified Lambda as Lambda
import qualified Hoas.Type as Hoas
import Prelude hiding ((.), id)

reify :: Cde (U (F Unit)) (U (F U64)) -> Word64
reify (C f) = case f (Thunk $ \w -> Unit :& Effect w) of
  Thunk t -> case t 0 of
    (U64 y :& _) -> y

newtype Cde a b = C (Data a -> Data b)

newtype Stk a b = S (Action a -> Action b)

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

instance Category Cde where
  id = C id
  C f . C g = C (f . g)

instance Category Stk where
  id = S id
  S f . S g = S (f . g)

instance Code Cde where
  absurd = C $ \x -> case x of {}
  C x ||| C y = C $ \env -> case env of
    L l -> x l
    R r -> y r
  left = C L
  right = C R

  unit = C $ const Unit
  lift (C x) = C $ \y -> Pair (x Unit) y

instance Stack Stk where

instance Cbpv Stk Cde where
  push (C f) = S $ \x -> f Unit :& x
  return (C f) = S $ \(x :& w) -> f x :& w

  thunk (S f) = C $ \x -> Thunk $ \w -> f (x :& Effect w)
  force (C f) = S $ \(x :& Effect w) -> case f x of
    Thunk t -> t w

  be (C x) f = C $ \env -> case f (C $ const (x env)) of
    C y -> y env

  pass (C x) = S $ \(Lam f) -> f (x Unit)
  zeta _ f = S $ \env -> Lam $ \x -> case f (C $ const x) of
    S y -> y env
  pop _ f = S $ \(h :& t) -> case f (C $ const h) of
    S y -> y t

  -- | fixme... not quite right..
  letTo (S x) f = S $ \env -> case x env of
    x' :& env' -> case f (C $ const x') of
          S y -> y env


  u64 x = C $ const (U64 x)
  constant t pkg name = case (t, pkg, name) of
     (Hoas.SU64 Hoas.:-> (Hoas.SU64 Hoas.:-> Hoas.SU64), "core", "add") -> addImpl
  lambdaIntrinsic x = case x of
     Lambda.AddIntrinsic -> addLambdaImpl
  cbpvIntrinsic x = case x of
     AddIntrinsic -> addCbpvImpl

addImpl :: Stk (F Unit) (AsAlgebra (Lambda.AsObject (Hoas.U64 Hoas.~> Hoas.U64 Hoas.~> Hoas.U64)))
addImpl = S $ \(Unit :& Effect w0) ->
              Lam $ \(Thunk x) -> Lam $ \(Thunk y) -> case x w0 of
                 U64 x' :& Effect w1 -> case y w1 of
                   U64 y' :& Effect w2 -> U64 (x' + y') :& Effect w2

addLambdaImpl :: Cde (U (AsAlgebra (Lambda.U64 Lambda.* Lambda.U64))) (U (AsAlgebra Lambda.U64))
addLambdaImpl = C $ \(Thunk input) -> undefined

addCbpvImpl :: Cde (U64 * U64) U64
addCbpvImpl = C $ \(Pair (U64 x) (U64 y)) -> U64 (x + y)
