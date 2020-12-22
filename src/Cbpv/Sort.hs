{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cbpv.Sort
  (SSet (..),
   SAlgebra (..),
    Set,
    U,
    Unit,
    Void,
    type (*),
    type (+),
    U64,
    Algebra,
    F,
    Empty,
    type (&),
    type (~>),
AsAlgebra,
asAlgebra,
KnownSet (..),
KnownAlgebra (..)
  )
where
import qualified Lambda.Type as Type

type Set = SetImpl

type Unit = 'Unit

type Void = 'Void

type (*) = 'Product

infixl 0 *

type (+) = 'Sum

infixl 0 +

type U64 = 'U64

type Algebra = AlgebraImpl

type Empty = 'Empty

type (~>) = 'Exp
infixr 9 ~>

type (&) = 'Asym

infixr 0 &

type U x = 'U x

type F x = x & Empty

data SetImpl = U Algebra | Unit | Void | Sum Set Set | Product Set Set | U64

data AlgebraImpl = Empty | Exp Set Algebra | Asym Set Algebra

data SSet a where
  SU64 :: SSet U64
  SVoid :: SSet Void
  SUnit :: SSet Unit
  SU :: SAlgebra a -> SSet (U a)
  (:+:) :: SSet a -> SSet b -> SSet (a + b)
  (:*:) :: SSet a -> SSet b -> SSet (a * b)

data SAlgebra a where
  SEmpty :: SAlgebra Empty
  (:&:) :: SSet a -> SAlgebra b -> SAlgebra (a & b)
  (:->) :: SSet a -> SAlgebra b -> SAlgebra (a ~> b)


type family AsAlgebra a where
  AsAlgebra (a Type.~> b) = U (AsAlgebra a) ~> AsAlgebra b
  AsAlgebra Type.Unit = F Unit
  AsAlgebra Type.Void = F Void
  AsAlgebra (a Type.* b) = U (AsAlgebra a) & U (AsAlgebra b) & Empty
  AsAlgebra (a Type.+ b) = F (U (AsAlgebra a) + U (AsAlgebra b))
  AsAlgebra Type.U64 = F U64

asAlgebra :: Type.ST a -> SAlgebra (AsAlgebra a)
asAlgebra t = case t of
  a Type.:-> b -> SU (asAlgebra a) :-> asAlgebra b
  a Type.:*: b -> SU (asAlgebra a) :&: (SU (asAlgebra b) :&: SEmpty)
  a Type.:+: b -> (SU (asAlgebra a) :+: SU (asAlgebra b)) :&: SEmpty
  Type.SU64 -> SU64 :&: SEmpty
  Type.SUnit -> SUnit :&: SEmpty
  Type.SVoid -> SVoid :&: SEmpty


class KnownSet t where
  inferSet :: SSet t
class KnownAlgebra t where
  inferAlgebra :: SAlgebra t

instance KnownSet 'Unit where
  inferSet = SUnit

instance KnownSet 'Void where
  inferSet = SVoid

instance KnownSet 'U64 where
  inferSet = SU64

instance (KnownSet a, KnownSet b) => KnownSet ('Product a b) where
  inferSet = inferSet :*: inferSet

instance KnownAlgebra a => KnownSet ('U a) where
  inferSet = SU inferAlgebra

instance KnownAlgebra 'Empty where
  inferAlgebra = SEmpty

instance (KnownSet a, KnownAlgebra b) => KnownAlgebra ('Asym a b) where
  inferAlgebra = inferSet :&: inferAlgebra
instance (KnownSet a, KnownAlgebra b) => KnownAlgebra ('Exp a b) where
  inferAlgebra = inferSet :-> inferAlgebra
