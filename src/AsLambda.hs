{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module AsLambda (PointFree, pointFree) where

import Control.Category
import Data.Maybe
import Data.Typeable ((:~:) (..))
import qualified Hoas.Bound as Bound
import qualified Hoas.Type as Type
import Id (Id)
import Lambda
import Lambda.HasExp
import Lambda.HasProduct
import Lambda.HasSum
import Lambda.Type
import Prelude hiding (curry, id, uncurry, (.), (<*>))

pointFree :: PointFree k a b -> k (AsObject a) (AsObject b)
pointFree (PointFree x) = out x

newtype PointFree k a b = PointFree (Pf k (AsObject a) (AsObject b))

instance Lambda k => Category (PointFree k) where
  id = PointFree id
  PointFree f . PointFree g = PointFree (f . g)

instance Lambda k => Bound.Bound (PointFree k) where
  PointFree f <*> PointFree x = PointFree (f <*> x)

  lam n t f = PointFree (curry me)
    where
      v = Var t n
      PointFree body = f (PointFree (mkVar v))
      me = case removeVar body v of
        Nothing -> body . second
        Just y -> y

  be n (PointFree x) t f = PointFree me
    where
      v = Var t n
      PointFree body = f (PointFree (mkVar v))
      me = case removeVar body v of
        Nothing -> body
        Just y -> y . (x &&& id)

  u64 x = PointFree (u64 x . unit)
  constant t pkg name = PointFree (constant t pkg name . unit)

instance HasProduct k => Category (Pf k) where
  id = lift0 id
  f . g = me
    where
      me =
        V
          { out = out f . out g,
            removeVar = \v -> case (removeVar f v, removeVar g v) of
              (Just f', Just g') -> Just $ f' . (first &&& g')
              (_, Just g') -> Just $ f . g'
              (Just f', _) -> Just $ f' . (first &&& (g . second))
              _ -> Nothing
          }

instance (HasExp k, HasSum k) => HasSum (Pf k) where
  absurd = lift0 absurd
  left = lift0 left
  right = lift0 right
  f ||| g = me
    where
      me =
        V
          { out = out f ||| out g,
            removeVar = \v -> case (removeVar f v, removeVar g v) of
              (Just f', Just g') -> Just $ uncurry (curry f' ||| curry g')
              (_, Just g') -> Just $ uncurry (curry (f . second) ||| curry g')
              (Just f', _) -> Just $ uncurry (curry f' ||| curry (g . second))
              _ -> Nothing
          }

instance HasProduct k => HasProduct (Pf k) where
  unit = lift0 unit
  first = lift0 first
  second = lift0 second
  f &&& g = me
    where
      me =
        V
          { out = out f &&& out g,
            removeVar = \v -> case (removeVar f v, removeVar g v) of
              (Just f', Just g') -> Just $ f' &&& g'
              (_, Just g') -> Just $ (f . second) &&& g'
              (Just f', _) -> Just $ f' &&& (g . second)
              _ -> Nothing
          }

instance (HasProduct k, HasExp k) => HasExp (Pf k) where
  curry f = me
    where
      me =
        V
          { out = curry (out f),
            removeVar = \v -> case removeVar f v of
              Just f' -> Just $ curry (f' . shuffle)
              _ -> Nothing
          }
  uncurry f = me
    where
      me =
        V
          { out = uncurry (out f),
            removeVar = \v -> case removeVar f v of
              Just f' -> Just $ uncurry f' . shuffle
              _ -> Nothing
          }

shuffle :: HasProduct k => k (v * (a * env)) (a * (v * env))
shuffle = (first . second) &&& (first &&& (second . second))

instance Lambda k => Lambda (Pf k) where
  u64 x = lift0 (u64 x)
  constant t pkg name = lift0 (constant t pkg name)

data Pf k (env :: T) (b :: T) = V
  { out :: k env b,
    removeVar :: forall v. Var v -> Maybe (Pf k ((AsObject v) * env) b)
  }

data Var a = Var (Type.ST a) Id

eqVar :: Var a -> Var b -> Maybe (a :~: b)
eqVar (Var t m) (Var t' n)
  | m == n = Type.eqT t t'
  | otherwise = Nothing

lift0 :: k a b -> Pf k a b
lift0 x = me
  where
    me =
      V
        { out = x,
          removeVar = const Nothing
        }

mkVar :: Lambda k => Var a -> Pf k x (AsObject a)
mkVar v@(Var _ n) = me
  where
    me =
      V
        { out = error ("free variable " ++ show n),
          removeVar = \maybeV -> case eqVar v maybeV of
            Nothing -> Nothing
            Just Refl -> Just first
        }
