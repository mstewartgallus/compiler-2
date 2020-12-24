{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cbpv.Sort
  (SSet,
   SAlgebra,
   SSort (..),
   Sort,
    Set,
    U,
    Unit,
    type (*),
    U64,
    Algebra,
    F,
    Empty,
    type (&),
    type (~>),
    AsAlgebra,
    asAlgebra,
    KnownSort (..)
  )
where
import qualified Ccc.Type as Type

type Unit = 'Unit

type (*) = 'Product

infixl 0 *

type U64 = 'U64

type Empty = 'Empty

type (~>) = 'Exp
infixr 9 ~>

type (&) = 'Asym

infixr 0 &

type U = 'U

type F x = x & Empty

data Tag = SetTag | AlgebraTag
type Set = Sort SetTag
type Algebra = Sort AlgebraTag

data Sort a where
  U :: Algebra -> Sort SetTag
  Unit :: Sort SetTag
  Product :: Set -> Set -> Sort SetTag

  Empty :: Sort AlgebraTag
  Exp :: Set -> Algebra -> Sort AlgebraTag
  Asym :: Set -> Algebra -> Sort AlgebraTag

  U64 :: Sort SetTag

data SSort t (a :: Sort t) where
  SU64 :: SSort SetTag U64
  SUnit :: SSort SetTag Unit
  SU :: SSort AlgebraTag a -> SSort SetTag (U a)
  (:*:) :: SSort SetTag a -> SSort SetTag b -> SSort SetTag (a * b)

  SEmpty :: SSort AlgebraTag Empty
  (:&:) :: SSort SetTag a -> SSort AlgebraTag b -> SSort AlgebraTag (a & b)
  (:->) :: SSort SetTag a -> SSort AlgebraTag b -> SSort AlgebraTag (a ~> b)

type SSet = SSort SetTag
type SAlgebra = SSort AlgebraTag

type family AsAlgebra a where
  AsAlgebra Type.Unit = F Unit
  AsAlgebra (a Type.* b) = F (U (AsAlgebra a) * U (AsAlgebra b))
  AsAlgebra (a Type.~> b) = U (AsAlgebra a) ~> AsAlgebra b
  AsAlgebra Type.U64 = F U64

asAlgebra :: Type.ST a -> SAlgebra (AsAlgebra a)
asAlgebra t = case t of
  a Type.:*: b -> (SU (asAlgebra a) :*: SU (asAlgebra b)) :&: SEmpty
  a Type.:-> b -> SU (asAlgebra a) :-> asAlgebra b
  Type.SU64 -> SU64 :&: SEmpty
  Type.SUnit -> SUnit :&: SEmpty

class KnownSort (a :: Sort t) where
  inferSort :: SSort t a

instance KnownSort 'Unit where
  inferSort = SUnit

instance KnownSort 'U64 where
  inferSort = SU64

instance (KnownSort a, KnownSort b) => KnownSort ('Product a b) where
  inferSort = inferSort :*: inferSort

instance KnownSort a => KnownSort ('U a) where
  inferSort = SU inferSort

instance KnownSort 'Empty where
  inferSort = SEmpty

instance (KnownSort a, KnownSort b) => KnownSort ('Asym a b) where
  inferSort = inferSort :&: inferSort
instance (KnownSort a, KnownSort b) => KnownSort ('Exp a b) where
  inferSort = inferSort :-> inferSort
