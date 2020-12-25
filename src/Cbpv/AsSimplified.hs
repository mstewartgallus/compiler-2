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
import Control.Category
import Cbpv.Sort
import qualified Cbpv.Hom as Hom
import Prelude hiding ((.), id, curry, uncurry, Monad (..), Either (..))

simplify :: Hom.Closed @SetTag a b -> Hom.Closed a b
simplify x = Hom.Closed (outC (simpC (Hom.fold x)))

data Stk f g (a :: Algebra) (b :: Algebra) where
  K :: f a b -> Stk f g a b

  IdK :: Category f => Stk f g a a
  ComposeK ::  Category f => Stk f g b c -> Stk f g a b -> Stk f g a c

  Force :: Cbpv f g => Cde f g a (U b) -> Stk f g (F a) b

  Pop :: Cbpv f g => SSet a -> (Cde f g Unit a -> Stk f g b c) -> Stk f g (a & b) c
  WhereIs :: Cbpv f g => Stk f g (a & b) c -> Cde f g Unit a -> Stk f g b c

  Zeta :: Cbpv f g => SSet a -> (Cde f g Unit a -> Stk f g b c) -> Stk f g b (a ~> c)
  App :: Cbpv f g => Stk f g b (a ~> c) -> Cde f g Unit a -> Stk f g b c

data Cde f g (a :: Set) (b :: Set) where
  C :: g a b -> Cde f g a b
  IdC :: Category g => Cde f g a a
  ComposeC ::  Category g => Cde f g b c -> Cde f g a b -> Cde f g a c

  Kappa :: Code g => SSet a -> (Cde f g Unit a -> Cde f g b c) -> Cde f g (a * b) c
  WhereIsK :: Code g => Cde f g (a * b) c -> Cde f g Unit a -> Cde f g b c

  Thunk :: Cbpv f g => Stk f g (F a) b -> Cde f g a (U b)

  Unit :: Code g => Cde f g a Unit

outC :: Cde f g a b -> g a b
outC expr = case expr of
  C x -> x
  IdC -> id
  ComposeC f g -> outC f . outC g

  Kappa t f -> kappa t (\x -> outC (f (C x)))
  WhereIsK f x -> whereIsK (outC f) (outC x)

  Thunk y -> thunk (outK y)

  Unit -> unit

outK :: Stk f g a b -> f a b
outK expr = case expr of
  K x -> x
  IdK -> id
  ComposeK f g -> outK f . outK g

  Force y -> force (outC y)

  Pop t f -> pop t (\x -> outK (f (C x)))
  WhereIs f x -> whereIs (outK f) (outC x)

  Zeta t f -> zeta t (\x -> outK (f (C x)))
  App f x -> app (outK f) (outC x)

recurseC :: Cde f g a b -> Cde f g a b
recurseC expr = case expr of
  C x -> C x
  IdC -> id
  ComposeC f g -> simpC f . simpC g

  Thunk y -> thunk (simpK y)

  Kappa t f -> kappa t (\x -> simpC (f x))
  WhereIsK f x -> whereIsK (simpC f) (simpC x)

  Unit -> unit

recurseK :: Stk f g a b -> Stk f g a b
recurseK expr = case expr of
  K x -> K x
  IdK -> id
  ComposeK f g -> simpK f . simpK g

  Force y -> force (simpC y)

  Pop t f -> pop t (\x -> simpK (f x))
  WhereIs f x -> whereIs (simpK f) (simpC x)

  Zeta t f -> zeta t (\x -> simpK (f x))
  App f x -> app (simpK f) (simpC x)

optC :: Cde f g a b -> Maybe (Cde f g a b)
optC expr = case expr of
  ComposeC IdC f -> Just f
  ComposeC f IdC -> Just f

  ComposeC Unit _ -> Just unit

  WhereIsK (ComposeC y f) x  -> Just (y . whereIsK f x)
  WhereIsK (Kappa _ f) x  -> Just (f x)

  ComposeC g (Kappa t f) -> Just $ kappa t $ \x -> g . f x

  Thunk (Force f) -> Just f

  _ -> Nothing

optK :: Stk f g a b -> Maybe (Stk f g a b)
optK expr = case expr of
  ComposeK IdK f -> Just f
  ComposeK f IdK -> Just f

  ComposeK g (Pop t f) -> Just $ pop t $ \x -> g . f x
  ComposeK (Zeta t f) g -> Just $ zeta t $ \x -> f x . g

  WhereIs (ComposeK y f) x  -> Just (y . whereIs f x)
  App (ComposeK f y) x  -> Just (app f x . y)

  WhereIs (Pop _ f) x  -> Just (f x)
  App (Zeta _ f) x -> Just (f x)

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

  whereIsK = WhereIsK
  kappa = Kappa

instance Cbpv f g => Cbpv (Stk f g) (Cde f g) where
  thunk = Thunk
  force = Force

  whereIs = WhereIs
  pop = Pop

  app = App
  zeta = Zeta

  u64 x = C (u64 x)
  constant t pkg name = K (constant t pkg name)
  cccIntrinsic x = C (cccIntrinsic x)
  cbpvIntrinsic x = C (cbpvIntrinsic x)
