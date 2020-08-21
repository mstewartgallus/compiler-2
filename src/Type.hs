{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Type (KnownT, inferT, eqT, ST (..), T, Void, Unit, type (~>), type (*), type (+), type U64, Value, Continuation, End) where

import Data.Kind (Type)
import Data.Typeable ((:~:) (..))

type Value (hom :: T -> T -> Type) a = forall x. hom x a

type Continuation (hom :: T -> T -> Type) a = forall x. hom a x

type End (hom :: T -> T -> Type) = forall x. hom x x

type T = TImpl

type Void = 'Void

type Unit = 'Unit

type (~>) = 'Exp

type (*) = 'Product

type (+) = 'Sum

type U64 = 'U64

infixr 9 ~>

infixl 0 *

infixl 0 +

data TImpl = U64 | Void | Unit | Sum T T | Product T T | Exp T T

data ST a where
  SU64 :: ST U64
  SVoid :: ST Void
  SUnit :: ST Unit
  (:*:) :: ST a -> ST b -> ST (a * b)
  (:+:) :: ST a -> ST b -> ST (a + b)
  (:->) :: ST a -> ST b -> ST (a ~> b)

class KnownT t where
  inferT :: ST t

instance KnownT 'U64 where
  inferT = SU64

instance KnownT 'Unit where
  inferT = SUnit

instance KnownT 'Void where
  inferT = SVoid

instance (KnownT a, KnownT b) => KnownT ('Product a b) where
  inferT = inferT :*: inferT

instance (KnownT a, KnownT b) => KnownT ('Sum a b) where
  inferT = inferT :+: inferT

instance (KnownT a, KnownT b) => KnownT ('Exp a b) where
  inferT = inferT :-> inferT

eqT :: ST a -> ST b -> Maybe (a :~: b)
eqT x y = case (x, y) of
  (SVoid, SVoid) -> Just Refl
  (SUnit, SUnit) -> Just Refl
  (SU64, SU64) -> Just Refl
  (x :*: y, x' :*: y') -> do
    Refl <- eqT x x'
    Refl <- eqT y y'
    return Refl
  (x :+: y, x' :+: y') -> do
    Refl <- eqT x x'
    Refl <- eqT y y'
    return Refl
  (x :-> y, x' :-> y') -> do
    Refl <- eqT x x'
    Refl <- eqT y y'
    return Refl
  _ -> Nothing

instance Show (ST a) where
  show expr = case expr of
    SU64 -> "U64"
    SVoid -> "Void"
    SUnit -> "Unit"
    x :*: y -> "(" ++ show x ++ " * " ++ show y ++ ")"
    x :-> y -> "(" ++ show x ++ " ~> " ++ show y ++ ")"
    x :+: y -> "(" ++ show x ++ " + " ++ show y ++ ")"
