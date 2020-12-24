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

  Pop :: Cbpv f g => SSet a -> (Cde f g Unit a -> Stk f g b c) -> Stk f g (a & b) c
  Push :: Cbpv f g => Cde f g Unit a -> Stk f g b (a & b)

  Zeta :: Cbpv f g => SSet a -> (Cde f g Unit a -> Stk f g b c) -> Stk f g b (a ~> c)
  Pass :: Cbpv f g => Cde f g Unit a -> Stk f g (a ~> b) b

data Cde f g (a :: Set) (b :: Set) where
  C :: g a b -> Cde f g a b
  IdC :: Category g => Cde f g a a
  ComposeC ::  Category g => Cde f g b c -> Cde f g a b -> Cde f g a c

  Kappa :: Code g => SSet a -> (Cde f g Unit a -> Cde f g b c) -> Cde f g (a * b) c
  Lift :: Code g => Cde f g Unit a -> Cde f g b (a * b)

  Thunk :: Cbpv f g => Stk f g (F a) b -> Cde f g a (U b)

  Unit :: Code g => Cde f g a Unit

outC :: Cde f g a b -> g a b
outC expr = case expr of
  C x -> x
  IdC -> id
  ComposeC f g -> outC f . outC g

  Kappa t f -> kappa t (\x -> outC (f (C x)))
  Lift x -> lift (outC x)

  Thunk y -> thunk (outK y)

  Unit -> unit

outK :: Stk f g a b -> f a b
outK expr = case expr of
  K x -> x
  IdK -> id
  ComposeK f g -> outK f . outK g

  Force y -> force (outC y)

  Pop t f -> pop t (\x -> outK (f (C x)))
  Push x -> push (outC x)

  Zeta t f -> zeta t (\x -> outK (f (C x)))
  Pass x -> pass (outC x)

recurseC :: Cde f g a b -> Cde f g a b
recurseC expr = case expr of
  C x -> C x
  IdC -> id
  ComposeC f g -> simpC f . simpC g

  Thunk y -> thunk (simpK y)

  Kappa t f -> kappa t (\x -> simpC (f x))
  Lift x -> lift (simpC x)

  Unit -> unit

recurseK :: Stk f g a b -> Stk f g a b
recurseK expr = case expr of
  K x -> K x
  IdK -> id
  ComposeK f g -> simpK f . simpK g

  Force y -> force (simpC y)

  Pop t f -> pop t (\x -> simpK (f x))
  Push x -> push (simpC x)

  Zeta t f -> zeta t (\x -> simpK (f x))
  Pass x -> pass (simpC x)

optC :: Cde f g a b -> Maybe (Cde f g a b)
optC expr = case expr of
  ComposeC IdC f -> Just f
  ComposeC f IdC -> Just f

  ComposeC Unit _ -> Just unit

  ComposeC (Kappa _ f) (Lift x)  -> Just (f x)

  ComposeC (ComposeC f g) h  -> Just $ f . (g . h)

  Thunk (Force f) -> Just f

  _ -> Nothing

optK :: Stk f g a b -> Maybe (Stk f g a b)
optK expr = case expr of
  ComposeK IdK f -> Just f
  ComposeK f IdK -> Just f

  ComposeK (Pop _ f) (Push x)  -> Just (f x)
  ComposeK (Pass x) (Zeta _ f)  -> Just (f x)

  ComposeK (ComposeK f g) h  -> Just $ f . (g . h)

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

  lift = Lift
  kappa = Kappa

instance Cbpv f g => Cbpv (Stk f g) (Cde f g) where
  thunk = Thunk
  force = Force

  push = Push
  pop = Pop

  pass = Pass
  zeta = Zeta

  u64 x = C (u64 x)
  constant t pkg name = K (constant t pkg name)
  cccIntrinsic x = C (cccIntrinsic x)
  cbpvIntrinsic x = C (cbpvIntrinsic x)
