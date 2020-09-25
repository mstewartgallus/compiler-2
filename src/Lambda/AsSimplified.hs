{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

-- | Simplify various identites such as:
-- force/thunk as inverses
-- id
module Lambda.AsSimplified (Expr, simplify) where

import Lambda
import Control.Category
import Lambda.HasExp
import Lambda.HasProduct
import Lambda.HasSum
import Lambda.Type
import Prelude hiding ((.), id, curry, uncurry, Monad (..), Either (..))

simplify :: Expr f a b -> f a b
simplify = out

data Expr f a b where
  E :: f a b -> Expr f a b

  Id :: Category f => Expr f a a
  Compose ::  Category f => Expr f b c -> Expr f a b -> Expr f a c

  Unit :: HasProduct f => Expr f a Unit
  First :: HasProduct f => Expr f (a * b) a
  Second :: HasProduct f => Expr f (a * b) b
  Fanout :: HasProduct f => Expr f c a -> Expr f c b -> Expr f c (a * b)

  Absurd :: HasSum f => Expr f Void a
  Left :: HasSum f => Expr f a (a + b)
  Right :: HasSum f => Expr f b (a + b)
  Fanin :: HasSum f => Expr f a c -> Expr f b c -> Expr f (a + b) c

out :: Expr f a b -> f a b
out expr = case expr of
  E x -> x
  Id -> id
  Compose f g -> out f . out g

  Unit -> unit
  First -> first
  Second -> second
  Fanout f g -> out f &&& out g

  Absurd -> absurd
  Left -> left
  Right -> right
  Fanin f g -> out f ||| out g

instance Category f => Category (Expr f) where
  id = Id
  Id . f = f
  f . Id = f

  _ . Absurd = absurd
  Fanin f _  . Left = f
  Fanin _ f . Right = f

  Unit . _ = unit
  First . Fanout f _ = f
  Second . Fanout _ f = f

  x . Fanin f g = (x . f) ||| (x . g)
  Fanout f g . x = (f . x) &&& (g . x)

  Compose f g . h  = f . (g . h)
  f . g = Compose f g

instance HasProduct f => HasProduct (Expr f) where
  unit = Unit
  First &&& Second = id
  f &&& g = Fanout f g
  first = First
  second = Second

instance HasSum f => HasSum (Expr f) where
  absurd = Absurd
  Left ||| Right = id
  f ||| g = Fanin f g
  left = Left
  right = Right

instance HasExp f => HasExp (Expr f) where
  curry f = E (curry (out f))
  uncurry f = E (uncurry (out f))

instance Lambda f => Lambda (Expr f) where
  u64 x = E (u64 x)
  add = E add
