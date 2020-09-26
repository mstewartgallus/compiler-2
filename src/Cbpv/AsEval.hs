{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cbpv.AsEval (reify, Stack, Code, Action, Data) where

import Cbpv
import Control.Category
import Data.Word
import Cbpv.Sort
import Prelude hiding ((.), id)

reify :: Code (U (F Unit)) (U (F U64)) -> Word64
reify (C f) = case f (Thunk $ \w -> Unit :& Effect w) of
  Thunk t -> case t 0 of
    (U64 y :& _) -> y

newtype Code a b = C (Data a -> Data b)

newtype Stack a b = S (Action a -> Action b)

data family Data (a :: Set)

data instance Data (U a) = Thunk (Int -> Action a)

data instance Data Unit = Unit
data instance Data Void
data instance Data (a * b) = Pair { firstOf :: (Data a), secondOf :: (Data b) }
data instance Data (a + b) = L (Data a) | R (Data b)
newtype instance Data U64 = U64 Word64

-- | Actions are CBPVs computations but we use a different name for brevity
data family Action (a :: Algebra)
data instance Action Empty = Effect Int
data instance Action (a & b) = Data a :& Action b
infixr 9 :&
newtype instance Action (a ~> b) = Lam (Data a -> Action b)

instance Category Code where
  id = C id
  C f . C g = C (f . g)

instance Category Stack where
  id = S id
  S f . S g = S (f . g)

instance Cbpv Stack Code where
  return (C f) = S $ \(x :& w) -> f x :& w

  thunk (S f) = C $ \x -> Thunk $ \w -> f (x :& Effect w)
  force (C f) = S $ \(x :& Effect w) -> case f x of
    Thunk t -> t w

  absurd = C $ \x -> case x of {}
  C x ||| C y = C $ \env -> case env of
    L l -> x l
    R r -> y r
  left = C L
  right = C R

  unit = C $ const Unit
  C x &&& C y = C $ \env -> Pair (x env) (y env)
  first = C firstOf
  second = C secondOf

  curry (S f) = S $ \env -> Lam $ \x -> f (x :& env)
  uncurry (S f) = S $ \(x :& env) -> case f env of
     Lam y -> y x

  pop = S $ \(a :& b :& c) -> Pair a b :& c
  push = S $ \(Pair a b :& c) -> a :& b :& c

  u64 x = C $ const (U64 x)
  constant t pkg name = S $ case (t, pkg, name) of
     (SU (SU64 :&: SEmpty) :-> (SU (SU64 :&: SEmpty) :-> (SU64 :&: SEmpty)),
      "core", "add") ->
          \(Unit :& Effect w0) ->
              Lam $ \(Thunk x) -> Lam $ \(Thunk y) -> case x w0 of
                 U64 x' :& Effect w1 -> case y w1 of
                   U64 y' :& Effect w2 -> U64 (x' + y') :& Effect w2
