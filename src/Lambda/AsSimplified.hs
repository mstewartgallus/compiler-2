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
import Lambda.HasLet
import Lambda.HasProduct
import Lambda.HasSum
import Lambda.Type
import Prelude hiding ((.), id, curry, uncurry, Monad (..), Either (..))

simplify :: Expr f a b -> f a b
simplify x = out (simp x)

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

  Curry :: HasExp f => Expr f (a * env) b -> Expr f env (a ~> b)
  Uncurry :: HasExp f => Expr f env (a ~> b) -> Expr f (a * env) b

simp :: Expr f a b -> Expr f a b
simp expr = case opt expr of
  Just x -> simp x
  Nothing -> recurse expr

opt :: Expr f a b -> Maybe (Expr f a b)
opt expr  = case expr of
  Fanout First Second -> Just id
  Fanin Left Right -> Just id

  Compose (Curry f) g -> Just $ curry (f . (first &&& (g . second)))
  Uncurry (Compose f g) -> Just $ uncurry f . (first &&& (g . second))

  Curry (Uncurry f) -> Just f
  Uncurry (Curry f) -> Just f

  Compose Id f -> Just f
  Compose f Id -> Just f

  Compose _ Absurd -> Just absurd
  Compose (Fanin f _) Left -> Just f
  Compose (Fanin _ f) Right -> Just f

  Compose Unit _ -> Just unit
  Compose First (Fanout f _) -> Just f
  Compose Second (Fanout _ f) -> Just f

  Compose x (Fanin f g) -> Just ((x . f) ||| (x . g))
  Compose (Fanout f g) x -> Just ((f . x) &&& (g . x))

  Compose (Compose f g) h  -> Just (f . (g . h))

  _ -> Nothing

recurse :: Expr f a b -> Expr f a b
recurse expr = case expr of
  E x -> E x
  Id -> id

  Compose f g -> simp f . simp g

  Unit -> unit
  First -> first
  Second -> second
  Fanout f g -> simp f &&& simp g

  Absurd -> absurd
  Left -> left
  Right -> right
  Fanin f g -> simp f ||| simp g

  Curry f -> curry (simp f)
  Uncurry f -> uncurry (simp f)

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

  Curry f -> curry (out f)
  Uncurry f -> uncurry (out f)

instance Category f => Category (Expr f) where
  id = Id
  (.) = Compose

instance HasProduct f => HasProduct (Expr f) where
  unit = Unit
  (&&&) = Fanout
  first = First
  second = Second

instance HasSum f => HasSum (Expr f) where
  absurd = Absurd
  (|||) = Fanin
  left = Left
  right = Right

instance HasExp f => HasExp (Expr f) where
  curry = Curry
  uncurry = Uncurry

instance HasLet f => HasLet (Expr f) where
  be t (E x) f = E $ be t x $ \x' -> out (f (E x'))

instance Lambda f => Lambda (Expr f) where
  u64 x = E (u64 x)
  constant t pkg name = E $ constant t pkg name
  lambdaConstant t pkg name = E $ lambdaConstant t pkg name
