{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Reorder (f . (g . h)) to ((f . g) . h)
module Cbpv.AsLeft (Stk, Cde, asLeft) where

import Cbpv
import Control.Category
import qualified Cbpv.Hom as Hom
import Cbpv.Sort
import Data.Kind
import Prelude hiding ((.), id)

asLeft :: Cde f g a b -> g a b
asLeft x = outC (simpC x)

data Stk f (g :: Set -> Set -> Type) (a :: Algebra) (b :: Algebra) where
  K :: f a b -> Stk f g a b

  IdK :: Category f => Stk f g a a
  ComposeK ::  Category f => Stk f g b c -> Stk f g a b -> Stk f g a c

data Cde (f :: Algebra -> Algebra -> Type) g (a :: Set) (b :: Set) where
  C :: g a b -> Cde f g a b

  IdC :: Category g => Cde f g a a
  ComposeC ::  Category g => Cde f g b c -> Cde f g a b -> Cde f g a c

outC :: Cde f g a b -> g a b
outC expr = case expr of
  C x -> x
  IdC -> id
  ComposeC f g -> outC f . outC g

outK :: Stk f g a b -> f a b
outK expr = case expr of
  K x -> x
  IdK -> id
  ComposeK f g -> outK f . outK g

recurseC :: Cde f g a b -> Cde f g a b
recurseC expr = case expr of
  C x -> C x
  IdC -> id
  ComposeC f g -> simpC f . simpC g

recurseK :: Stk f g a b -> Stk f g a b
recurseK expr = case expr of
  K x -> K x
  IdK -> id
  ComposeK f g -> simpK f . simpK g

optC :: Cde f g a b -> Maybe (Cde f g a b)
optC expr = case expr of
  ComposeC IdC f -> Just f
  ComposeC f IdC -> Just f

  ComposeC (ComposeC f g) h  -> Just $ f . (g . h)

  _ -> Nothing

optK :: Stk f g a b -> Maybe (Stk f g a b)
optK expr = case expr of
  ComposeK IdK f -> Just f
  ComposeK f IdK -> Just f

  ComposeK (ComposeK f g) h  -> Just $ f . (g . h)

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
  unit = C unit

  whereIsK f x = C (whereIsK (outC (simpC f)) (outC (simpC x)))
  kappa t f = C $ kappa t $ \x ->
    outC (simpC (f (C x)))

instance Cbpv f g => Cbpv (Stk f g) (Cde f g) where
  thunk x = C (thunk (outK (simpK x)))
  force x = K (force (outC (simpC x)))

  whereIs f x = K (whereIs (outK (simpK f)) (outC (simpC x)))
  pop t f = K $ pop t $ \x ->
    outK (simpK (f (C x)))

  app f x = K (app (outK (simpK f)) (outC (simpC x)))
  zeta t f = K $ zeta t $ \x ->
    outK (simpK (f (C x)))

  u64 x = C (u64 x)
  constant t pkg name = K (constant t pkg name)
  cccIntrinsic x = C (cccIntrinsic x)
  cbpvIntrinsic x = C (cbpvIntrinsic x)
