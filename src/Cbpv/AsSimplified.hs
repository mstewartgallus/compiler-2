{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Simplify various identites such as:
-- force/thunk as inverses
-- id
module Cbpv.AsSimplified (Stack, Code, simplify) where

import Cbpv
import qualified Cbpv.AsCost as AsCost
import qualified Cbpv.AsDup as AsDup
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, curry, uncurry, Monad (..), Either (..))

simplify :: Code f g a b -> g a b
simplify = outC

data Stack f g (a :: Algebra) (b :: Algebra) where
  K :: f a b -> Stack f g a b
  IdK :: Category f => Stack f g a a
  Force :: Cbpv f g => Code f g a (U b) -> Stack f g (F a) b
  Return :: Cbpv f g => Code f g a b -> Stack f g (F a) (F b)

data Code f g (a :: Set) (b :: Set) where
  C :: g a b -> Code f g a b
  IdC :: Category g => Code f g a a
  Thunk :: Cbpv f g => Stack f g (F a) b -> Code f g a (U b)

  Unit :: Cbpv f g => Code f g a Unit
  First :: Cbpv f g => Code f g (a * b) a
  Second :: Cbpv f g => Code f g (a * b) b
  Fanout :: Cbpv f g => Code f g c a -> Code f g c b -> Code f g c (a * b)

  Absurd :: Cbpv f g => Code f g Void a
  Left :: Cbpv f g => Code f g a (a + b)
  Right :: Cbpv f g => Code f g b (a + b)
  Fanin :: Cbpv f g => Code f g a c -> Code f g b c -> Code f g (a + b) c

outC :: Code f g a b -> g a b
outC expr = case expr of
  C x -> x
  IdC -> id

  Thunk y -> thunk (outK y)

  Unit -> unit
  First -> first
  Second -> second
  Fanout f g -> outC f &&& outC g

  Absurd -> absurd
  Left -> left
  Right -> right
  Fanin f g -> outC f ||| outC g

outK :: Stack f g a b -> f a b
outK expr = case expr of
  K x -> x
  IdK -> id
  Return x -> return (outC x)
  Force y -> force (outC y)

instance (Category f, Category g) => Category (Stack f g) where
  id = IdK
  IdK . f = f
  f . IdK = f
  Return f . Return g = Return (f . g)

  Force f . Return g = Force (f . g)

  f . g = K (outK f . outK g)

instance (Category f, Category g) => Category (Code f g) where
  id = IdC
  IdC . f = f
  f . IdC = f

  _ . Absurd = Absurd
  Fanin f _  . Left = f
  Fanin _ f . Right = f

  Unit . _ = Unit
  First . Fanout f _ = f
  Second . Fanout _ f = f

  Thunk x . y = Thunk (x . Return y)

  x . Fanin f g = Fanin (x . f) (x . g)
  Fanout f g . x = Fanout (f . x) (g . x)

  f . g = C (outC f . outC g)

instance Cbpv f g => Cbpv (Stack f g) (Code f g) where
  thunk (Force f) = f
  thunk f = Thunk f

  force (Thunk f) = f
  force f = Force f

  Return f `to` Return x = Return (x . Fanout IdC f)
  f `to` x = K (outK f `to` outK x)

  return IdC = IdK
  return x = Return x

  unit = Unit
  First &&& Second = IdC
  f &&& g = Fanout f g
  first = First
  second = Second

  absurd = Absurd
  Left ||| Right = IdC
  f ||| g = Fanin f g
  left = Left
  right = Right

  assocOut = K assocOut
  assocIn = K assocIn

  curry f = K (curry (outK f))
  uncurry f = K (uncurry (outK f))

  u64 x = C (u64 x)
  add = C add
  addLazy = K addLazy
