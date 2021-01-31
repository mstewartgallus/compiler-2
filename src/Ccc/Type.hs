{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}

module Ccc.Type (T, Unit, type (~>), type (*), type U64, AsObject, ObjectOf (..), Tagged (..), KnownT (..), Foo (..), Bar (..)) where
import qualified Lam.Type as Lam
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

class Tag t where
  foldTag :: Tagged v => t a -> v a

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

newtype Foo t a = Foo (t (AsObject a))
instance Tagged t => Lam.Tagged (Foo t) where
  u64Tag = Foo u64Tag
  unitTag = Foo unitTag
  expTag (Foo a) (Foo b) = Foo (expTag a b)

data Bar a = KnownT a => Bar

instance Tagged Bar where
  u64Tag = Bar
  unitTag = Bar
  expTag Bar Bar = Bar

newtype ObjectOf a = ObjectOf (Dict (KnownT (AsObject a)))


type family AsObject a = r | r -> a where
  AsObject (a Lam.~> b) = AsObject a ~> AsObject b
  AsObject Lam.U64 = U64
  AsObject Lam.Unit = Unit

instance Lam.Tagged ObjectOf where
  u64Tag = ObjectOf Dict
  unitTag = ObjectOf Dict
  expTag (ObjectOf Dict) (ObjectOf Dict) = ObjectOf Dict
