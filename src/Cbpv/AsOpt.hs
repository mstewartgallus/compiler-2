{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Remove duplicate force/thunk pairs
module Cbpv.AsOpt (Stack, Code, opt) where

import Cbpv
import qualified Cbpv.AsCost as AsCost
import qualified Cbpv.AsDup as AsDup
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, curry, uncurry, Monad (..))

data Stack f g (a :: Algebra) (b :: Algebra) where
  K :: f a b -> Stack f g a b
  IdK :: Category f => Stack f g a a
  Return :: Cbpv f g => g a b -> Stack f g (F a) (F b)
  Force :: Cbpv f g => g a (U b) -> Stack f g (F a) b

data Code f g (a :: Set) (b :: Set) where
  C :: g a b -> Code f g a b
  IdC :: Category g => Code f g a a
  Thunk :: Cbpv f g => f (F a) b -> Code f g a (U b)

outC :: Code f g a b -> g a b
outC expr = case expr of
  C x -> x
  IdC -> id
  Thunk y -> thunk y

outK :: Stack f g a b -> f a b
outK expr = case expr of
  K x -> x
  IdK -> id
  Return x -> return x
  Force y -> force y

opt :: Code f g a b -> g a b
opt = outC

instance (Category f, Category g) => Category (Stack f g) where
  id = IdK
  IdK . f = f
  f . IdK = f
  Return f . Return g = Return (f . g)
  f . g = K (outK f . outK g)

instance (Category f, Category g) => Category (Code f g) where
  id = IdC
  IdC . f = f
  f . IdC = f
  f . g = C (outC f . outC g)

instance Cbpv f g => Cbpv (Stack f g) (Code f g) where
  thunk (Force f) = C f
  thunk f = Thunk (outK f)

  force (Thunk f) = K f
  force f = Force (outC f)

  f `to` x = K (outK f `to` outK x)

  return IdC = IdK
  return f = Return (outC f)

  unit = C unit
  f &&& g = C (outC f &&& outC g)
  first = C first
  second = C second

  absurd = C absurd
  f ||| g = C (outC f ||| outC g)
  left = C left
  right = C right

  assocOut = K assocOut
  assocIn = K assocIn

  curry f = K (curry (outK f))
  uncurry f = K (uncurry (outK f))

  u64 x = C (u64 x)
  add = C add
  addLazy = K addLazy
