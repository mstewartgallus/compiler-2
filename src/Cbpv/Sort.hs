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
asAlgebra
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
  AsAlgebra (a Type.* b) = F (U (AsAlgebra a) * U (AsAlgebra b))
  AsAlgebra (a Type.+ b) = F (U (AsAlgebra a) + U (AsAlgebra b))
  AsAlgebra Type.U64 = F U64

asAlgebra :: Type.ST a -> SAlgebra (AsAlgebra a)
asAlgebra t = case t of
  a Type.:-> b -> SU (asAlgebra a) :-> asAlgebra b
  a Type.:*: b -> (SU (asAlgebra a) :*: SU (asAlgebra b)) :&: SEmpty
  a Type.:+: b -> (SU (asAlgebra a) :+: SU (asAlgebra b)) :&: SEmpty
  Type.SU64 -> SU64 :&: SEmpty
  Type.SUnit -> SUnit :&: SEmpty
  Type.SVoid -> SVoid :&: SEmpty
