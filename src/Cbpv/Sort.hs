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
   Tag (..),
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
    type (~.),
    AsAlgebra,
    asAlgebra,
    toKnownSort,
eqSort,
    KnownSort (..)
  )
where
import qualified Ccc.Type as Type
import Dict
import Data.Typeable ((:~:) (..))

type Unit = 'Unit

type (*) = 'Product

infixl 0 *

type U64 = 'U64

type Empty = 'Empty

type (~.) = 'Thunk

type (~>) = 'Exp
infixr 9 ~>

type (&) = 'Asym

infixr 0 &

type U = 'Thunk Empty

type F x = x & Empty

data Tag = SetTag | AlgebraTag
type Set = Sort SetTag
type Algebra = Sort AlgebraTag

data Sort a where
  Thunk :: Algebra -> Algebra -> Sort SetTag
  Unit :: Sort SetTag
  Product :: Set -> Set -> Sort SetTag

  Empty :: Sort AlgebraTag
  Exp :: Set -> Algebra -> Sort AlgebraTag
  Asym :: Set -> Algebra -> Sort AlgebraTag

  U64 :: Sort SetTag

data SSort t (a :: Sort t) where
  SU64 :: SSort SetTag U64
  SUnit :: SSort SetTag Unit
  (:-.) :: SSort AlgebraTag a -> SSort AlgebraTag b -> SSort SetTag (a ~. b)
  (:*:) :: SSort SetTag a -> SSort SetTag b -> SSort SetTag (a * b)

  SEmpty :: SSort AlgebraTag Empty
  (:&:) :: SSort SetTag a -> SSort AlgebraTag b -> SSort AlgebraTag (a & b)
  (:->) :: SSort SetTag a -> SSort AlgebraTag b -> SSort AlgebraTag (a ~> b)

type SSet = SSort SetTag
type SAlgebra = SSort AlgebraTag

type family AsAlgebra a = r | r -> a where
  AsAlgebra Type.Unit = F Unit
  AsAlgebra (a Type.* b) = F (U (AsAlgebra a) * U (AsAlgebra b))
  AsAlgebra (a Type.~> b) = U (AsAlgebra a) ~> AsAlgebra b
  AsAlgebra Type.U64 = F U64

thunk = (:-.) SEmpty

asAlgebra :: Type.ST a -> SAlgebra (AsAlgebra a)
asAlgebra t = case t of
  a Type.:*: b -> (thunk (asAlgebra a) :*: thunk (asAlgebra b)) :&: SEmpty
  a Type.:-> b -> thunk (asAlgebra a) :-> asAlgebra b
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

instance (KnownSort a, KnownSort b) => KnownSort ('Thunk a b) where
  inferSort = inferSort :-. inferSort

instance KnownSort 'Empty where
  inferSort = SEmpty

instance (KnownSort a, KnownSort b) => KnownSort ('Asym a b) where
  inferSort = inferSort :&: inferSort
instance (KnownSort a, KnownSort b) => KnownSort ('Exp a b) where
  inferSort = inferSort :-> inferSort

toKnownSort :: SSort t a -> Dict (KnownSort a)
toKnownSort x = case x of
  SU64 -> Dict
  SUnit -> Dict
  x :*: y -> case (toKnownSort x, toKnownSort y) of
    (Dict, Dict) -> Dict
  x :-. y -> case (toKnownSort x, toKnownSort y) of
    (Dict, Dict) -> Dict

  SEmpty -> Dict
  x :&: y -> case (toKnownSort x, toKnownSort y) of
    (Dict, Dict) -> Dict
  x :-> y -> case (toKnownSort x, toKnownSort y) of
    (Dict, Dict) -> Dict

eqSort :: SSort t a -> SSort t b -> Maybe (a :~: b)
eqSort x y = case (x, y) of
  (SU64, SU64) -> pure Refl
  (SUnit, SUnit) -> pure Refl
  (a :*: b, a' :*: b') -> do
    Refl <- eqSort a a'
    Refl <- eqSort b b'
    pure Refl
  (a :-. b, a' :-. b') -> do
    Refl <- eqSort a a'
    Refl <- eqSort b b'
    pure Refl

  (SEmpty, SEmpty) -> pure Refl
  (a :&: b, a' :&: b') -> do
    Refl <- eqSort a a'
    Refl <- eqSort b b'
    pure Refl
  (a :-> b, a' :-> b') -> do
    Refl <- eqSort a a'
    Refl <- eqSort b b'
    pure Refl
