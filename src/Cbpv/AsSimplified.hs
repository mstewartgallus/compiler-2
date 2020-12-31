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

  Pop :: (KnownSort a, KnownSort b, KnownSort c, Cbpv f g) => SSet a -> (Cde f g Unit a -> Stk f g b c) -> Stk f g (a & b) c
  Lift :: (KnownSort a, KnownSort b, Cbpv f g) => Cde f g Unit a -> Stk f g b (a & b)

  Zeta :: (KnownSort a, KnownSort b, KnownSort c, Cbpv f g) => SSet a -> (Cde f g Unit a -> Stk f g b c) -> Stk f g b (a ~> c)
  Pass :: (KnownSort a, KnownSort b, Cbpv f g) => Cde f g Unit a -> Stk f g (a ~> b) b

data Cde f g (a :: Set) (b :: Set) where
  C :: g a b -> Cde f g a b
  IdC :: (KnownSort a, Category g) => Cde f g a a
  ComposeC ::  (KnownSort a, KnownSort b, KnownSort c, Category g) => Cde f g b c -> Cde f g a b -> Cde f g a c

  Fst :: (KnownSort a, KnownSort b, Code g) => Cde f g (a * b) a
  Snd :: (KnownSort a, KnownSort b, Code g) => Cde f g (a * b) b
  Fanout :: (KnownSort a, KnownSort b, KnownSort x, Code g) => Cde f g x a -> Cde f g x b -> Cde f g x (a * b)

  Thunk :: (KnownSort a, KnownSort b, Cbpv f g) => SSet a -> (Cde f g Unit a -> Stk f g Empty b) -> Cde f g a (U b)

  Unit :: (KnownSort a, Code g) => Cde f g a Unit

outC :: Cde f g a b -> g a b
outC expr = case expr of
  C x -> x
  IdC -> id
  ComposeC f g -> outC f . outC g

  Fanout x y -> outC x &&& outC y
  Fst -> fst
  Snd -> snd

  Thunk t f -> thunk t (\x -> outK (f (C x)))

  Unit -> unit

outK :: Stk f g a b -> f a b
outK expr = case expr of
  K x -> x
  IdK -> id
  ComposeK f g -> outK f . outK g

  Force x -> force (outC x)

  Pop t f -> pop t (\x -> outK (f (C x)))
  Lift x -> lift (outC x)

  Zeta t f -> zeta t (\x -> outK (f (C x)))
  Pass x -> pass (outC x)

recurseC :: Cde f g a b -> Cde f g a b
recurseC expr = case expr of
  C x -> C x
  IdC -> id
  ComposeC f g -> simpC f . simpC g

  Thunk t f -> thunk t (\x -> simpK (f x))

  Fanout x y -> simpC x &&& simpC y
  Unit -> unit
  Fst -> fst
  Snd -> snd

recurseK :: Stk f g a b -> Stk f g a b
recurseK expr = case expr of
  K x -> K x
  IdK -> id
  ComposeK f g -> simpK f . simpK g

  Force x -> force (simpC x)

  Pop t f -> pop t (\x -> simpK (f x))
  Lift x -> lift (simpC x)

  Zeta t f -> zeta t (\x -> simpK (f x))
  Pass x -> pass (simpC x)

optC :: Cde f g a b -> Maybe (Cde f g a b)
optC expr = case expr of
  ComposeC IdC f -> Just f
  ComposeC f IdC -> Just f

  ComposeC Unit _ -> Just unit

  ComposeC (Fanout x y) z -> Just ((x . z) &&& (y . z))

  ComposeC Fst (Fanout x _) -> Just x
  ComposeC Snd (Fanout _ x) -> Just x

  ComposeC (Thunk t f) x -> Just (thunk undefined (\env -> f (x . env)))
  _ -> Nothing

optK :: Stk f g a b -> Maybe (Stk f g a b)
optK expr = case expr of
  ComposeK IdK f -> Just f
  ComposeK f IdK -> Just f

  ComposeK g (Pop t f) -> Just $ pop t $ \x -> g . f x
  ComposeK (Zeta t f) g -> Just $ zeta t $ \x -> f x . g

  ComposeK (Pop _ f) (Lift x) -> Just (f x)
  ComposeK (Pass x) (Zeta _ f) -> Just (f x)

  Force (Thunk _ f) -> Just (f Unit)

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
  (&&&) = Fanout
  fst = Fst
  snd = Snd

instance Cbpv f g => Cbpv (Stk f g) (Cde f g) where
  thunk = Thunk
  force = Force

  lift = Lift
  pop = Pop

  pass = Pass
  zeta = Zeta

  u64 x = C (u64 x)
  constant t pkg name = K (constant t pkg name)
  cccIntrinsic x = C (cccIntrinsic x)
  cbpvIntrinsic x = C (cbpvIntrinsic x)
