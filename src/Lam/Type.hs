{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Lam.Type (KnownT, inferT, eqT, ST (..), T, type (~>), type Unit, type U64) where

import Data.Text.Prettyprint.Doc
import Data.Typeable ((:~:) (..))

type (~>) = 'Exp

type U64 = 'U64
type Unit = 'Unit

infixr 9 ~>

data T = Unit | U64 | Exp T T

data ST a where
  SUnit :: ST Unit
  SU64 :: ST U64
  (:->) :: ST a -> ST b -> ST (a ~> b)

class KnownT t where
  inferT :: ST t

instance KnownT 'Unit where
  inferT = SUnit

instance KnownT 'U64 where
  inferT = SU64

instance (KnownT a, KnownT b) => KnownT ('Exp a b) where
  inferT = inferT :-> inferT

eqT :: ST a -> ST b -> Maybe (a :~: b)
eqT l r = case (l, r) of
  (SUnit, SUnit) -> Just Refl
  (SU64, SU64) -> Just Refl
  (x :-> y, x' :-> y') -> do
    Refl <- eqT x x'
    Refl <- eqT y y'
    return Refl
  _ -> Nothing

instance Pretty (ST a) where
  pretty expr = case expr of
    SUnit -> pretty "1"
    SU64 -> pretty "u64"
    x :-> y -> parens $ sep [pretty x, pretty "→", pretty y]
