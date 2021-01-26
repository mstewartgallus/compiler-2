{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FunctionalDependencies #-}
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
Tagged (..),
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

thunk :: Tagged set alg => alg a -> set (Empty ~. a)
thunk = thunkTag emptyTag

asAlgebra :: Tagged set alg => Type.ST a -> alg (AsAlgebra a)
asAlgebra t = case t of
  a Type.:*: b -> (thunk (asAlgebra a) `tupleTag` thunk (asAlgebra b)) `asymTag` emptyTag
  a Type.:-> b -> thunk (asAlgebra a) `expTag` asAlgebra b
  Type.SU64 -> u64Tag `asymTag` emptyTag
  Type.SUnit -> unitTag `asymTag` emptyTag

class KnownSet a where
  inferSet :: Tagged set alg => set a
class KnownAlgebra a where
  inferAlgebra :: Tagged set alg => alg a

class Tagged set alg | set -> alg, alg -> set where
  unitTag :: set Unit
  u64Tag :: set U64
  tupleTag :: set a -> set b -> set (a * b)
  thunkTag :: alg a -> alg b -> set (a ~. b)

  emptyTag :: alg Empty
  asymTag :: set a -> alg b -> alg (a & b)
  expTag :: set a -> alg b -> alg (a ~> b)

instance Tagged SSet SAlgebra where
  unitTag = SUnit
  u64Tag = SU64
  tupleTag = (:*:)
  thunkTag = (:-.)

  emptyTag = SEmpty
  asymTag = (:&:)
  expTag = (:->)

instance KnownSet 'Unit where
  inferSet = unitTag

instance KnownSet 'U64 where
  inferSet = u64Tag

instance (KnownSet a, KnownSet b) => KnownSet ('Product a b) where
  inferSet = tupleTag inferSet inferSet

instance (KnownAlgebra a, KnownAlgebra b) => KnownSet ('Thunk a b) where
  inferSet = thunkTag inferAlgebra inferAlgebra

instance KnownAlgebra 'Empty where
  inferAlgebra = emptyTag

instance (KnownSet a, KnownAlgebra b) => KnownAlgebra ('Asym a b) where
  inferAlgebra = asymTag inferSet inferAlgebra
instance (KnownSet a, KnownAlgebra b) => KnownAlgebra ('Exp a b) where
  inferAlgebra = expTag inferSet inferAlgebra

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
