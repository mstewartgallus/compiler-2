{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Simplify various identites such as:
-- force/thunk as inverses
-- id
module Cbpv.AsSimplified (Stk, Cde, simplify) where

import Cbpv
import Control.Category
import Cbpv.Sort
import Prelude hiding ((.), id, curry, uncurry, Monad (..), Either (..))

simplify :: Cde f g a b -> g a b
simplify x = outC (simpC x)

data Stk f g (a :: Algebra) (b :: Algebra) where
  K :: f a b -> Stk f g a b

  IdK :: Category f => Stk f g a a
  ComposeK ::  Category f => Stk f g b c -> Stk f g a b -> Stk f g a c

  Force :: Cbpv f g => Cde f g a (U b) -> Stk f g (F a) b

  Return :: Cbpv f g => Cde f g a b -> Stk f g (F a) (F b)

data Cde f g (a :: Set) (b :: Set) where
  C :: g a b -> Cde f g a b
  IdC :: Category g => Cde f g a a
  ComposeC ::  Category g => Cde f g b c -> Cde f g a b -> Cde f g a c
  Thunk :: Cbpv f g => Stk f g (F a) b -> Cde f g a (U b)

  Unit :: Code g => Cde f g a Unit

  Absurd :: Code g => Cde f g Void a
  Left :: Code g => Cde f g a (a + b)
  Right :: Code g => Cde f g b (a + b)
  Fanin :: Code g => Cde f g a c -> Cde f g b c -> Cde f g (a + b) c

outC :: Cde f g a b -> g a b
outC expr = case expr of
  C x -> x
  IdC -> id
  ComposeC f g -> outC f . outC g

  Thunk y -> thunk (outK y)

  Unit -> unit

  Absurd -> absurd
  Left -> left
  Right -> right
  Fanin f g -> outC f ||| outC g

outK :: Stk f g a b -> f a b
outK expr = case expr of
  K x -> x
  IdK -> id
  ComposeK f g -> outK f . outK g
  Return x -> return (outC x)
  Force y -> force (outC y)

recurseC :: Cde f g a b -> Cde f g a b
recurseC expr = case expr of
  C x -> C x
  IdC -> id
  ComposeC f g -> simpC f . simpC g

  Thunk y -> thunk (simpK y)

  Unit -> unit

  Absurd -> absurd
  Left -> left
  Right -> right
  Fanin f g -> simpC f ||| simpC g

recurseK :: Stk f g a b -> Stk f g a b
recurseK expr = case expr of
  K x -> K x
  IdK -> id
  ComposeK f g -> simpK f . simpK g
  Return x -> return (simpC x)
  Force y -> force (simpC y)

optC :: Cde f g a b -> Maybe (Cde f g a b)
optC expr = case expr of
  ComposeC IdC f -> Just f
  ComposeC (Fanin f _) Left -> Just f
  ComposeC (Fanin _ f) Right -> Just f

  ComposeC Unit _ -> Just unit

  ComposeC (Thunk f) g -> Just $ thunk (f . return g)

  ComposeC (ComposeC f g) h  -> Just $ f . (g . h)

  ComposeC f IdC -> Just f
  ComposeC _ Absurd -> Just absurd
  ComposeC x (Fanin f g) -> Just $ (x . f) ||| (x . g)

  Thunk (Force f) -> Just f

  Fanin Left Right -> Just id

  _ -> Nothing

optK :: Stk f g a b -> Maybe (Stk f g a b)
optK expr = case expr of
  ComposeK IdK f -> Just f
  ComposeK f IdK -> Just f

  ComposeK (Force f) (Return g) -> Just $ force (f . g)

  ComposeK (Return f) (Return g)  -> Just $ return (f . g)

  ComposeK (ComposeK f g) h  -> Just $ f . (g . h)

  Return IdC -> Just id

  Force (Thunk f) -> Just f

  _ -> Nothing

simpC :: Cde f g a b -> Cde f g a b
simpC expr = case optC expr of
  Just x -> simpC x
  Nothing -> recurseC expr

simpK :: Stk f g a b -> Stk f g a b
simpK expr = case optK expr of
  Just x -> simpK x
  Nothing -> recurseK expr

instance Category f => Category (Stk f g) where
  id = IdK
  (.) = ComposeK

instance Category g => Category (Cde f g) where
  id = IdC
  (.) = ComposeC

instance Stack f => Stack (Stk f g) where

instance Code g => Code (Cde f g) where
  unit = Unit

  absurd = Absurd
  (|||) = Fanin
  left = Left
  right = Right

  lift x = C $ lift (outC x)
  kappa t f = C $ kappa t $ \x' -> outC (f (C x'))

instance Cbpv f g => Cbpv (Stk f g) (Cde f g) where
  return = Return

  thunk = Thunk
  force = Force

  push x = K $ push (outC x)
  pass x = K $ pass (outC x)

  be x f = C $ be (outC x) $ \x' -> outC (f (C x'))
  letTo x f = K $ letTo (outK x) $ \x' -> outK (f (C x'))
  zeta t f = K $ zeta t $ \x' -> outK (f (C x'))
  pop t f = K $ pop t $ \x' -> outK (f (C x'))
  u64 x = C (u64 x)
  constant t pkg name = K (constant t pkg name)
  lambdaIntrinsic x = C (lambdaIntrinsic x)
  cbpvIntrinsic x = C (cbpvIntrinsic x)
