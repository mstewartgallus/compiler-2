{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

-- | Simplify various identities
module Ccc.AsSimplified (simplify) where

import Ccc
import Control.Category
import Ccc.Hom
import Ccc.Type
import Prelude hiding ((.), id, curry, uncurry, Monad (..), Either (..))

simplify :: Closed a b -> Closed a b
simplify x = Closed (out (simp (fold x)))

data Expr f a b where
  E :: f a b -> Expr f a b

  Id :: Category f => Expr f a a
  Compose ::  Category f => Expr f b c -> Expr f a b -> Expr f a c

  Unit :: Ccc f => Expr f a Unit

  Kappa :: Ccc f => ST a -> (Expr f Unit a -> Expr f b c) -> Expr f (a * b) c
  WhereIs :: Ccc f => Expr f (a * b) c -> Expr f Unit a -> Expr f b c

  Zeta :: Ccc f => ST a -> (Expr f Unit a -> Expr f b c) -> Expr f b (a ~> c)
  App :: Ccc f => Expr f b (a ~> c) -> Expr f Unit a -> Expr f b c

simp :: Expr f a b -> Expr f a b
simp expr = case opt expr of
  Just x -> simp x
  Nothing -> recurse expr

opt :: Expr f a b -> Maybe (Expr f a b)
opt expr  = case expr of
  Compose Id f -> Just f
  Compose f Id -> Just f

  Compose Unit _ -> Just unit

  App (Zeta _ f) x -> Just (f x)
  WhereIs (Kappa _ f) x -> Just (f x)

  WhereIs (Compose y f) x -> Just (y . whereIs f x)

  Compose (Compose f g) h  -> Just (f . (g . h))

  _ -> Nothing

recurse :: Expr f a b -> Expr f a b
recurse expr = case expr of
  E x -> E x
  Id -> id

  Compose f g -> simp f . simp g

  Unit -> unit

  Zeta t f -> zeta t (\x -> simp (f x))
  App f x -> app (simp f) (simp x)

  Kappa t f -> kappa t (\x -> simp (f x))
  WhereIs f  x -> whereIs (simp f) (simp x)

out :: Expr f a b -> f a b
out expr = case expr of
  E x -> x
  Id -> id
  Compose f g -> out f . out g

  Unit -> unit

  Zeta t f -> zeta t (\x -> out (f (E x)))
  App f x -> app (out f) (out x)

  Kappa t f -> kappa t (\x -> out (f (E x)))
  WhereIs f x -> whereIs (out f) (out x)

instance Category f => Category (Expr f) where
  id = Id
  (.) = Compose

instance Ccc f => Ccc (Expr f) where
  unit = Unit

  whereIs = WhereIs
  kappa = Kappa

  zeta = Zeta
  app = App

  u64 x = E (u64 x)
  constant t pkg name = E $ constant t pkg name
  cccIntrinsic x = E $ cccIntrinsic x
