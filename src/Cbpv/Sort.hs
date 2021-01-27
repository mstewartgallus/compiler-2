{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cbpv.Sort
  (KnownSetDict,
   KnownAlgebraDict,
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
    AlgebraOf (..),
    toKnownSet,
    toKnownAlgebra,
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

type family AsAlgebra a = r | r -> a where
  AsAlgebra Type.Unit = F Unit
  AsAlgebra (a Type.* b) = F (U (AsAlgebra a) * U (AsAlgebra b))
  AsAlgebra (a Type.~> b) = U (AsAlgebra a) ~> AsAlgebra b
  AsAlgebra Type.U64 = F U64

thunk :: Tagged set alg => alg a -> set (Empty ~. a)
thunk = thunkTag emptyTag

newtype AlgebraOf a = AO { asAlgebra :: forall set alg. Tagged set alg => alg (AsAlgebra a) }

instance Type.Tagged AlgebraOf where
  unitTag = AO (unitTag `asymTag` emptyTag)
  u64Tag = AO (u64Tag `asymTag` emptyTag)
  tupleTag (AO a) (AO b) = AO ((thunk a `tupleTag` thunk b) `asymTag` emptyTag)
  expTag (AO a) (AO b) = AO (thunk a `expTag` b)

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

newtype KnownSetDict a = KS { toKnownSet :: Dict (KnownSet a) }
newtype KnownAlgebraDict a = KA { toKnownAlgebra :: Dict (KnownAlgebra a) }

instance Tagged KnownSetDict KnownAlgebraDict where
  unitTag = KS Dict
  u64Tag = KS Dict
  tupleTag (KS Dict) (KS Dict) = KS Dict
  thunkTag (KA Dict) (KA Dict) = KS Dict

  emptyTag = KA Dict
  asymTag (KS Dict) (KA Dict) = KA Dict
  expTag (KS Dict) (KA Dict) = KA Dict
