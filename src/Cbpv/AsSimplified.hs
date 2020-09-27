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
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, curry, uncurry, Monad (..), Either (..))

simplify :: Code f g a b -> g a b
simplify = outC

data Stack f g (a :: Algebra) (b :: Algebra) where
  K :: f a b -> Stack f g a b

  IdK :: Category f => Stack f g a a
  ComposeK ::  Category f => Stack f g b c -> Stack f g a b -> Stack f g a c

  Force :: Cbpv f g => Code f g a (U b) -> Stack f g (F a) b

  Return :: Cbpv f g => Code f g a b -> Stack f g (F a) (F b)

  Push :: Cbpv f g => Stack f g ((a * b) & c) (a & (b & c))
  Pop :: Cbpv f g => Stack f g (a & (b & c)) ((a * b) & c)

  Curry :: Cbpv f g => Stack f g (a & env) b -> Stack f g env (a ~> b)
  Uncurry :: Cbpv f g => Stack f g env (a ~> b) -> Stack f g (a & env) b

data Code f g (a :: Set) (b :: Set) where
  C :: g a b -> Code f g a b
  IdC :: Category g => Code f g a a
  ComposeC ::  Category g => Code f g b c -> Code f g a b -> Code f g a c
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
  ComposeC f g -> outC f . outC g

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
  ComposeK f g -> outK f . outK g
  Push -> push
  Pop -> pop
  Curry f -> curry (outK f)
  Uncurry f -> uncurry (outK f)
  Return x -> return (outC x)
  Force y -> force (outC y)

instance (Category f, Category g) => Category (Stack f g) where
  id = IdK
  IdK . f = f
  f . IdK = f

  Force f . Return g = force (f . g)
  Return f . Return g = return (f . g)

  ComposeK f g . h  = f . (g . h)
  f . g = ComposeK f g

instance (Category f, Category g) => Category (Code f g) where
  id = IdC
  IdC . f = f
  f . IdC = f

  _ . Absurd = absurd
  Fanin f _  . Left = f
  Fanin _ f . Right = f

  Unit . _ = unit
  First . Fanout f _ = f
  Second . Fanout _ f = f

  x . Fanin f g = (x . f) ||| (x . g)
  Fanout f g . x = (f . x) &&& (g . x)

  ComposeC f g . h  = f . (g . h)
  f . g = ComposeC f g

instance Cbpv f g => Cbpv (Stack f g) (Code f g) where
  return IdC = id
  return x = Return x

  thunk (ComposeK f (Return g)) = thunk f . g
  thunk (Force f) = f
  thunk f = Thunk f

  force (ComposeC f g) = force f . return g
  force (Thunk f) = f
  force f = Force f

  unit = Unit
  First &&& Second = id
  f &&& g = Fanout f g
  first = First
  second = Second

  absurd = Absurd
  Left ||| Right = id
  f ||| g = Fanin f g
  left = Left
  right = Right

  pop = Pop
  push = Push

  curry (Uncurry f) = f
  curry f = Curry f

  uncurry (Curry f) = f
  uncurry f = Uncurry f

  u64 x = C (u64 x)
  constant t pkg name = K (constant t pkg name)
  lambdaConstant t pkg name = K (lambdaConstant t pkg name)
  cbpvConstant t pkg name = K (cbpvConstant t pkg name)
