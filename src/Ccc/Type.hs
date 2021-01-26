{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Ccc.Type (ST (..), T, Unit, type (~>), type (*), type U64, AsObject, asObject, ObjectOf (..), KnownDict (..), Tagged (..), KnownT (..)) where
import qualified Lam.Type as Type
import Dict

type Unit = 'Unit

type (~>) = 'Exp

type (*) = 'Product

type U64 = 'U64

infixr 9 ~>

infixl 0 *

data T = U64 | Unit | Product T T | Exp T T

class Tagged t where
  u64Tag :: t U64
  unitTag :: t Unit
  tupleTag :: t a -> t b -> t (a * b)
  expTag :: t a -> t b -> t (a ~> b)

class KnownT a where
  inferT :: Tagged t => t a

instance KnownT 'Unit where
  inferT = unitTag

instance KnownT 'U64 where
  inferT = u64Tag

instance (KnownT a, KnownT b) => KnownT ('Product a b) where
  inferT = tupleTag inferT inferT

instance (KnownT a, KnownT b) => KnownT ('Exp a b) where
  inferT = expTag inferT inferT

newtype KnownDict a = KD { toKnownT :: Dict (KnownT a) }

instance Tagged KnownDict where
  u64Tag = KD Dict
  unitTag = KD Dict
  tupleTag (KD Dict) (KD Dict) = KD Dict
  expTag (KD Dict) (KD Dict) = KD Dict

newtype ObjectOf t a = O { asObject :: t (AsObject a) }

type family AsObject a = r | r -> a where
  AsObject (a Type.~> b) = AsObject a ~> AsObject b
  AsObject Type.U64 = U64
  AsObject Type.Unit = Unit

instance Tagged t => Type.Tagged (ObjectOf t) where
  u64Tag = O u64Tag
  unitTag = O unitTag
  expTag (O a) (O b) = O (a `expTag` b)

instance Tagged ST where
  unitTag = SUnit
  u64Tag = SU64
  tupleTag = (:*:)
  expTag = (:->)

data ST a where
  SU64 :: ST U64
  SUnit :: ST Unit
  (:*:) :: ST a -> ST b -> ST (a * b)
  (:->) :: ST a -> ST b -> ST (a ~> b)
