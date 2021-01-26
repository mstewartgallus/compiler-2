{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
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
    toKnownSet,
toKnownAlgebra,
-- eqSort,
    KnownSet (..),
KnownAlgebra (..)
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

data Set = Unit | Thunk Algebra Algebra | Product Set Set | U64

data Algebra = Empty | Exp Set Algebra | Asym Set Algebra

data SSet a where
  SU64 :: SSet U64
  SUnit :: SSet Unit
  (:-.) :: SAlgebra a -> SAlgebra b -> SSet (a ~. b)
  (:*:) :: SSet a -> SSet b -> SSet (a * b)

data SAlgebra a where
  SEmpty :: SAlgebra Empty
  (:&:) :: SSet a -> SAlgebra b -> SAlgebra (a & b)
  (:->) :: SSet a -> SAlgebra b -> SAlgebra (a ~> b)

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

class KnownSet a where
  inferSet :: SSet a
class KnownAlgebra a where
  inferAlgebra :: SAlgebra a

instance KnownSet 'Unit where
  inferSet = SUnit

instance KnownSet 'U64 where
  inferSet = SU64

instance (KnownSet a, KnownSet b) => KnownSet ('Product a b) where
  inferSet = inferSet :*: inferSet

instance (KnownAlgebra a, KnownAlgebra b) => KnownSet ('Thunk a b) where
  inferSet = inferAlgebra :-. inferAlgebra

instance KnownAlgebra 'Empty where
  inferAlgebra = SEmpty

instance (KnownSet a, KnownAlgebra b) => KnownAlgebra ('Asym a b) where
  inferAlgebra = inferSet :&: inferAlgebra
instance (KnownSet a, KnownAlgebra b) => KnownAlgebra ('Exp a b) where
  inferAlgebra = inferSet :-> inferAlgebra

toKnownSet :: SSet a -> Dict (KnownSet a)
toKnownSet x = case x of
  SU64 -> Dict
  SUnit -> Dict
  x :*: y -> case (toKnownSet x, toKnownSet y) of
    (Dict, Dict) -> Dict
  x :-. y -> case (toKnownAlgebra x, toKnownAlgebra y) of
    (Dict, Dict) -> Dict

toKnownAlgebra :: SAlgebra a -> Dict (KnownAlgebra a)
toKnownAlgebra x = case x of
  SEmpty -> Dict
  x :&: y -> case (toKnownSet x, toKnownAlgebra y) of
    (Dict, Dict) -> Dict
  x :-> y -> case (toKnownSet x, toKnownAlgebra y) of
    (Dict, Dict) -> Dict

-- eqSort :: SSort t a -> SSort t b -> Maybe (a :~: b)
-- eqSort x y = case (x, y) of
--   (SU64, SU64) -> pure Refl
--   (SUnit, SUnit) -> pure Refl
--   (a :*: b, a' :*: b') -> do
--     Refl <- eqSort a a'
--     Refl <- eqSort b b'
--     pure Refl
--   (a :-. b, a' :-. b') -> do
--     Refl <- eqSort a a'
--     Refl <- eqSort b b'
--     pure Refl

--   (SEmpty, SEmpty) -> pure Refl
--   (a :&: b, a' :&: b') -> do
--     Refl <- eqSort a a'
--     Refl <- eqSort b b'
--     pure Refl
--   (a :-> b, a' :-> b') -> do
--     Refl <- eqSort a a'
--     Refl <- eqSort b b'
--     pure Refl
