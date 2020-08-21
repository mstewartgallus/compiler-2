{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Sort
  ( Set,
    U,
    Unit,
    type (*),
    type (+),
    U64,
    SSet (..),
    KnownSet,
    inferSet,
    eqSet,
    Algebra,
    F,
    Void,
    Initial,
    type (~>),
    type (&),
    SAlgebra (..),
    KnownAlgebra,
    inferAlgebra,
    eqAlgebra,
  )
where

import Data.Kind (Type)
import Data.Typeable ((:~:) (..))

type Set = SetImpl

type Unit = 'Unit

type (*) = 'Product

infixl 0 *

type (+) = 'Sum

infixl 0 +

type U64 = 'U64

type Algebra = AlgebraImpl

type Initial = 'Initial

type Void = 'Void

type (~>) = 'Exp

infixr 9 ~>

-- assymetric tensor product
type (&) = 'Asym

-- Not sure about this
type U x = 'U x

type F x = x & Initial

infixl 0 &

data SetImpl = U Algebra | Unit | Sum Set Set | Product Set Set | U64

data AlgebraImpl = Initial | Void | Exp Set Algebra | Asym Set Algebra

data SSet a where
  SU :: SAlgebra a -> SSet (U a)
  SUnit :: SSet Unit
  SU64 :: SSet U64
  (:*:) :: SSet a -> SSet b -> SSet (a * b)
  (:+:) :: SSet a -> SSet b -> SSet (a + b)

data SAlgebra a where
  SVoid :: SAlgebra Void
  SInitial :: SAlgebra Initial
  (:->) :: SSet a -> SAlgebra b -> SAlgebra (a ~> b)
  (:&) :: SSet a -> SAlgebra b -> SAlgebra (a & b)

class KnownSet t where
  inferSet :: SSet t

class KnownAlgebra t where
  inferAlgebra :: SAlgebra t

instance KnownAlgebra a => KnownSet ('U a) where
  inferSet = SU inferAlgebra

instance KnownSet 'Unit where
  inferSet = SUnit

instance (KnownSet a, KnownSet b) => KnownSet ('Product a b) where
  inferSet = inferSet :*: inferSet

instance (KnownSet a, KnownSet b) => KnownSet ('Sum a b) where
  inferSet = inferSet :+: inferSet

instance KnownSet 'U64 where
  inferSet = SU64

instance KnownAlgebra 'Void where
  inferAlgebra = SVoid

instance KnownAlgebra 'Initial where
  inferAlgebra = SInitial

instance (KnownSet a, KnownAlgebra b) => KnownAlgebra ('Exp a b) where
  inferAlgebra = inferSet :-> inferAlgebra

instance (KnownSet a, KnownAlgebra b) => KnownAlgebra ('Asym a b) where
  inferAlgebra = inferSet :& inferAlgebra

eqAlgebra :: SAlgebra a -> SAlgebra b -> Maybe (a :~: b)
eqAlgebra x y = case (x, y) of
  (SInitial, SInitial) -> Just Refl
  (SVoid, SVoid) -> Just Refl
  (a :-> b, a' :-> b') -> do
    Refl <- eqSet a a'
    Refl <- eqAlgebra b b'
    return Refl
  (a :& b, a' :& b') -> do
    Refl <- eqSet a a'
    Refl <- eqAlgebra b b'
    return Refl
  _ -> Nothing

eqSet :: SSet a -> SSet b -> Maybe (a :~: b)
eqSet x y = case (x, y) of
  (SU64, SU64) -> Just Refl
  (SUnit, SUnit) -> Just Refl
  (SU x, SU x') -> do
    Refl <- eqAlgebra x x'
    return Refl
  (a :*: b, a' :*: b') -> do
    Refl <- eqSet a a'
    Refl <- eqSet b b'
    return Refl
  (a :+: b, a' :+: b') -> do
    Refl <- eqSet a a'
    Refl <- eqSet b b'
    return Refl
  _ -> Nothing

instance Show (SSet a) where
  show expr = case expr of
    SU x -> "(U " ++ show x ++ ")"
    SUnit -> "Unit"
    SU64 -> "U64"
    x :*: y -> "(" ++ show x ++ " × " ++ show y ++ ")"
    x :+: y -> "(" ++ show x ++ " + " ++ show y ++ ")"

instance Show (SAlgebra a) where
  show expr = case expr of
    SInitial -> "Initial"
    SVoid -> "Void"
    x :-> y -> "(" ++ show x ++ " → " ++ show y ++ ")"
    x :& y -> "(" ++ show x ++ " ⊗ " ++ show y ++ ")"