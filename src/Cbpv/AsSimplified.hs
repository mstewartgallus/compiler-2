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
simplify x = outC (simpC x)

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

recurseC :: Code f g a b -> Code f g a b
recurseC expr = case expr of
  C x -> C x
  IdC -> id
  ComposeC f g -> simpC f . simpC g

  Thunk y -> thunk (simpK y)

  Unit -> unit
  First -> first
  Second -> second
  Fanout f g -> simpC f &&& simpC g

  Absurd -> absurd
  Left -> left
  Right -> right
  Fanin f g -> simpC f ||| simpC g

recurseK :: Stack f g a b -> Stack f g a b
recurseK expr = case expr of
  K x -> K x
  IdK -> id
  ComposeK f g -> simpK f . simpK g
  Push -> push
  Pop -> pop
  Curry f -> curry (simpK f)
  Uncurry f -> uncurry (simpK f)
  Return x -> return (simpC x)
  Force y -> force (simpC y)

optC :: Code f g a b -> Maybe (Code f g a b)
optC expr = case expr of
  ComposeC IdC f -> Just f
  ComposeC (Fanin f _) Left -> Just f
  ComposeC (Fanin _ f) Right -> Just f

  ComposeC Unit _ -> Just unit
  ComposeC First (Fanout f _) -> Just f
  ComposeC Second (Fanout _ f) -> Just f

  ComposeC (Fanout f g) x -> Just $ (f . x) &&& (g . x)
  ComposeC (Thunk f) g -> Just $ thunk (f . return g)

  ComposeC (ComposeC f g) h  -> Just $ f . (g . h)

  ComposeC f IdC -> Just f
  ComposeC _ Absurd -> Just absurd
  ComposeC x (Fanin f g) -> Just $ (x . f) ||| (x . g)

  Thunk (Force f) -> Just f

  Fanout First Second -> Just id
  Fanin Left Right -> Just id

  _ -> Nothing

optK :: Stack f g a b -> Maybe (Stack f g a b)
optK expr = case expr of
  ComposeK IdK f -> Just f
  ComposeK f IdK -> Just f

  ComposeK (Force f) (Return g) -> Just $ force (f . g)

  ComposeK Pop Push -> Just id
  ComposeK Push Pop -> Just id

  ComposeK (Return f) (Return g)  -> Just $ return (f . g)

  ComposeK (ComposeK f g) h  -> Just $ f . (g . h)

  Return IdC -> Just id

  Force (Thunk f) -> Just f

  Curry (Uncurry f) -> Just f
  Uncurry (Curry f) -> Just f

  _ -> Nothing

simpC :: Code f g a b -> Code f g a b
simpC expr = case optC expr of
  Just x -> simpC x
  Nothing -> recurseC expr

simpK :: Stack f g a b -> Stack f g a b
simpK expr = case optK expr of
  Just x -> simpK x
  Nothing -> recurseK expr

instance Category f => Category (Stack f g) where
  id = IdK
  (.) = ComposeK

instance Category g => Category (Code f g) where
  id = IdC
  (.) = ComposeC

instance Cbpv f g => Cbpv (Stack f g) (Code f g) where
  return = Return

  thunk = Thunk
  force = Force

  unit = Unit
  (&&&) = Fanout
  first = First
  second = Second

  absurd = Absurd
  (|||) = Fanin
  left = Left
  right = Right

  pop = Pop
  push = Push

  curry = Curry
  uncurry = Uncurry

  be x f = C $ be (outC x) $ \x' -> outC (f (C x'))
  letTo x f = K $ letTo (outK x) $ \x' -> outK (f (C x'))

  u64 x = C (u64 x)
  constant t pkg name = K (constant t pkg name)
  lambdaConstant t pkg name = K (lambdaConstant t pkg name)
  cbpvConstant t pkg name = K (cbpvConstant t pkg name)
