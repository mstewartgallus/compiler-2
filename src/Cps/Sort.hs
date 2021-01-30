{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cps.Sort
  ( Set,
    U,
    Unit,
    Void,
    type (*),
    U64,
    Algebra,
    F,
    Empty,
    type (\\),
    type (|-),
    type (~.),
    SetAsCps,
    AlgAsCps,
    CpsOfSet (..),
    CpsOfAlg (..),
    Tagged (..),
    KnownSet (..),
    KnownAlgebra (..)
  )
where
import qualified Cbpv.Sort as Cbpv
import Dict

type Unit = 'Unit
type Void = 'Void

type (*) = 'Product

infixl 0 *

type U64 = 'U64

type Empty = 'Empty

type (~.) = 'Thunk

type (|-) = 'Coexp
infixr 9 |-

type (\\) = 'Asym

infixr 0 \\

type U = 'Thunk Empty

type F x = x \\ Empty

data Set = Void | Unit | Thunk Algebra Algebra | Product Set Set | U64
data Algebra = Empty | Coexp Set Algebra | Asym Set Algebra

type family AlgAsCps a = r | r -> a where
  -- not sure...
  AlgAsCps Cbpv.Empty = Empty
  -- emptyTag :: alg Empty
  -- asymTag :: set a -> alg b -> alg (a \\ b)
  AlgAsCps (a Cbpv.& b) = SetAsCps a \\ AlgAsCps b
  AlgAsCps (a Cbpv.~> b) = SetAsCps a |- AlgAsCps b

type family SetAsCps a = r | r -> a where
  SetAsCps Cbpv.Unit = Void
  SetAsCps Cbpv.U64 = U64
  -- FIXME not sure
  SetAsCps (a Cbpv.* b) = (SetAsCps a * SetAsCps b)
  -- thunkTag :: alg a -> alg b -> set (a ~. b)


newtype CpsOfAlg a = CpsOfAlg (Dict (KnownAlgebra (AlgAsCps a)))
newtype CpsOfSet a = CpsOfSet (Dict (KnownSet (SetAsCps a)))

instance Cbpv.Tagged CpsOfSet CpsOfAlg where
  unitTag = CpsOfSet Dict
  u64Tag = CpsOfSet Dict
  tupleTag (CpsOfSet Dict) (CpsOfSet Dict) = CpsOfSet Dict
  -- thunkTag :: alg a -> alg b -> set (a ~. b)

  emptyTag = CpsOfAlg Dict
  asymTag (CpsOfSet Dict) (CpsOfAlg Dict) = CpsOfAlg Dict
  expTag (CpsOfSet Dict) (CpsOfAlg Dict) = CpsOfAlg Dict

class KnownSet a where
  inferSet :: Tagged set alg => set a
class KnownAlgebra a where
  inferAlgebra :: Tagged set alg => alg a

class Tagged set alg | set -> alg, alg -> set where
  voidTag :: set Void
  unitTag :: set Unit
  u64Tag :: set U64
  tupleTag :: set a -> set b -> set (a * b)
  thunkTag :: alg a -> alg b -> set (a ~. b)

  emptyTag :: alg Empty
  asymTag :: set a -> alg b -> alg (a \\ b)
  coexpTag :: set a -> alg b -> alg (a |- b)

instance KnownSet 'Void where
  inferSet = voidTag

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
instance (KnownSet a, KnownAlgebra b) => KnownAlgebra ('Coexp a b) where
  inferAlgebra = coexpTag inferSet inferAlgebra
