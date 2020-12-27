{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Ccc.Type (ST (..), T, Unit, type (~>), type (*), type U64, AsObject, asObject, KnownT (..)) where
import qualified Lam.Type as Type
import Data.Text.Prettyprint.Doc

type Unit = 'Unit

type (~>) = 'Exp

type (*) = 'Product

type U64 = 'U64

infixr 9 ~>

infixl 0 *

data T = U64 | Unit | Product T T | Exp T T

data ST a where
  SU64 :: ST U64
  SUnit :: ST Unit
  (:*:) :: ST a -> ST b -> ST (a * b)
  (:->) :: ST a -> ST b -> ST (a ~> b)


type family AsObject a = r | r -> a where
  AsObject (a Type.~> b) = AsObject a ~> AsObject b
  AsObject Type.U64 = U64
  AsObject Type.Unit = Unit

asObject :: Type.ST a -> ST (AsObject a)
asObject t = case t of
  Type.SU64 -> SU64
  Type.SUnit -> SUnit
  a Type.:-> b -> asObject a :-> asObject b

instance Pretty (ST a) where
  pretty expr = case expr of
    SUnit -> pretty "1"
    SU64 -> pretty "u64"
    x :*: y -> parens $ sep [pretty x, pretty "×", pretty y]
    x :-> y -> parens $ sep [pretty x, pretty "→", pretty y]

class KnownT t where
  inferT :: ST t

instance KnownT 'Unit where
  inferT = SUnit

instance KnownT 'U64 where
  inferT = SU64

instance (KnownT a, KnownT b) => KnownT ('Product a b) where
  inferT = inferT :*: inferT

instance (KnownT a, KnownT b) => KnownT ('Exp a b) where
  inferT = inferT :-> inferT
