{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Simplify various identites such as:
-- force/thunk as inverses
-- id
module Cbpv.AsSimplified (simplify) where

import Cbpv
import Cbpv.Sort
import qualified Cbpv.Hom as Hom
import Prelude hiding ((.), id, fst, snd)

simplify :: Hom.Closed @SetTag a b -> Hom.Closed a b
simplify x = Hom.Closed (outC (simpC (Hom.fold x)))

data Stk f g (a :: Algebra) (b :: Algebra) where
  K :: f a b -> Stk f g a b

  IdK :: (KnownSort a, Category f) => Stk f g a a
  ComposeK :: (KnownSort a, KnownSort b, KnownSort c, Category f) => Stk f g b c -> Stk f g a b -> Stk f g a c

  Force :: (KnownSort a, Cbpv f g) => Cde f g Unit (U a) -> Stk f g Empty a

  Pop :: (KnownSort a, KnownSort b, KnownSort c, Cbpv f g) => (Cde f g Unit a -> Stk f g b c) -> Stk f g (a & b) c
  Push :: (KnownSort a, KnownSort b, Cbpv f g) => Cde f g Unit a -> Stk f g b (a & b)

  Zeta :: (KnownSort a, KnownSort b, KnownSort c, Cbpv f g) => (Cde f g Unit a -> Stk f g b c) -> Stk f g b (a ~> c)
  Pass :: (KnownSort a, KnownSort b, Cbpv f g) => Cde f g Unit a -> Stk f g (a ~> b) b

data Cde f g (a :: Set) (b :: Set) where
  C :: g a b -> Cde f g a b
  IdC :: (KnownSort a, Category g) => Cde f g a a
  ComposeC ::  (KnownSort a, KnownSort b, KnownSort c, Category g) => Cde f g b c -> Cde f g a b -> Cde f g a c

  Kappa :: (KnownSort a, KnownSort b, KnownSort c, Code g) => (Cde f g Unit a -> Cde f g b c) -> Cde f g (a * b) c
  Lift :: (KnownSort a, KnownSort b, Code g) => Cde f g Unit a -> Cde f g b (a * b)

  Thunk :: (KnownSort a, KnownSort b, Cbpv f g) => (Cde f g Unit a -> Stk f g Empty b) -> Cde f g a (U b)

  Unit :: (KnownSort a, Code g) => Cde f g a Unit

outC :: Cde f g a b -> g a b
outC expr = case expr of
  C x -> x
  IdC -> id
  ComposeC f g -> outC f . outC g

  Kappa f -> kappa (\x -> outC (f (C x)))
  Lift x -> lift (outC x)

  Thunk f -> thunk (\x -> outK (f (C x)))

  Unit -> unit

outK :: Stk f g a b -> f a b
outK expr = case expr of
  K x -> x
  IdK -> id
  ComposeK f g -> outK f . outK g

  Force x -> force (outC x)

  Pop f -> pop (\x -> outK (f (C x)))
  Push x -> push (outC x)

  Zeta f -> zeta (\x -> outK (f (C x)))
  Pass x -> pass (outC x)

recurseC :: Cde f g a b -> Cde f g a b
recurseC expr = case expr of
  C x -> C x
  IdC -> id
  ComposeC f g -> simpC f . simpC g

  Thunk f -> thunk (\x -> simpK (f x))

  Unit -> unit

  Kappa f -> kappa (\x -> simpC (f x))
  Lift x -> lift (simpC x)

recurseK :: Stk f g a b -> Stk f g a b
recurseK expr = case expr of
  K x -> K x
  IdK -> id
  ComposeK f g -> simpK f . simpK g

  Force x -> force (simpC x)

  Pop f -> pop (\x -> simpK (f x))
  Push x -> push (simpC x)

  Zeta f -> zeta (\x -> simpK (f x))
  Pass x -> pass (simpC x)

optC :: Cde f g a b -> Maybe (Cde f g a b)
optC expr = case expr of
  ComposeC IdC f -> Just f
  ComposeC f IdC -> Just f

  ComposeC Unit _ -> Just unit

  ComposeC (Kappa f) (Lift x) -> Just (f x)
  ComposeC (Thunk f) x -> Just (thunk (\env -> f (x . env)))
  _ -> Nothing

optK :: Stk f g a b -> Maybe (Stk f g a b)
optK expr = case expr of
  ComposeK IdK f -> Just f
  ComposeK f IdK -> Just f

  ComposeK g (Pop f) -> Just $ pop $ \x -> g . f x
  ComposeK (Zeta f) g -> Just $ zeta $ \x -> f x . g

  ComposeK (Pop f) (Push x) -> Just (f x)

  Force (Thunk f) -> Just (f Unit)

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
  constant pkg name = K (constant pkg name)
  cccIntrinsic x = K (cccIntrinsic x)
  cbpvIntrinsic x = C (cbpvIntrinsic x)
