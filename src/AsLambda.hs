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
import qualified Hoas as Hoas
import qualified Hoas.Type as Type
import Lambda
import Lambda.HasExp
import Lambda.HasLet
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

instance Lambda k => Hoas.Hoas (PointFree k) where
  PointFree f <*> PointFree x = PointFree (f <*> x)

  lam t f = PointFree (curry me)
    where
      me = be (asObject t) $ \x' -> case f (PointFree x') of
        PointFree y -> y

  be (PointFree x) t f = PointFree (me . (x &&& id))
    where
      me = be (asObject t) $ \x' -> case f (PointFree x') of
        PointFree y -> y

  u64 x = PointFree (u64 x . unit)
  constant t pkg name = PointFree (constant t pkg name . unit)

instance (HasProduct k, HasLet k) => HasLet (Pf k) where
  be t f = me
    where
      me =
        V
          { out = be t $ \x' -> out (f (V x'))
          }

instance HasProduct k => Category (Pf k) where
  id = lift0 id
  f . g = me
    where
      me =
        V
          { out = out f . out g
          }

instance (HasExp k, HasSum k) => HasSum (Pf k) where
  absurd = lift0 absurd
  left = lift0 left
  right = lift0 right
  f ||| g = me
    where
      me =
        V
          { out = out f ||| out g
          }

instance HasProduct k => HasProduct (Pf k) where
  unit = lift0 unit
  first = lift0 first
  second = lift0 second
  f &&& g = me
    where
      me =
        V
          { out = out f &&& out g
          }

instance (HasProduct k, HasExp k) => HasExp (Pf k) where
  curry f = me
    where
      me =
        V
          { out = curry (out f)
          }
  uncurry f = me
    where
      me =
        V
          { out = uncurry (out f)
          }

shuffle :: HasProduct k => k (v * (a * env)) (a * (v * env))
shuffle = (first . second) &&& (first &&& (second . second))

instance Lambda k => Lambda (Pf k) where
  u64 x = lift0 (u64 x)
  constant t pkg name = lift0 (constant t pkg name)

data Pf k (env :: T) (b :: T) = V
  { out :: k env b
  }

lift0 :: k a b -> Pf k a b
lift0 x = me
  where
    me =
      V
        { out = x
        }
