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
pointFree (Pf x) = x

newtype PointFree k a b = Pf (k (AsObject a) (AsObject b))

instance Lambda k => Category (PointFree k) where
  id = Pf id
  Pf f . Pf g = Pf (f . g)

instance Lambda k => Hoas.Hoas (PointFree k) where
  Pf f <*> Pf x = Pf (apply f x)

  lam t f = Pf $
    zeta (asObject t) $ \x -> case f (Pf x) of
      Pf y -> y

  be (Pf x) t f = Pf me
    where
      me = be (asObject t) x $ \x' -> case f (Pf x') of
        Pf y -> y

  u64 x = Pf (u64 x)
  constant t pkg name = Pf (constant t pkg name)

-- fixme... figure out ST..
apply :: Lambda k => k x (a ~> b) -> k x a -> k x b
apply f x =
  be undefined x $ \x' ->
    be undefined f $ \f' ->
      unit
        >>> f'
        >>> pass x'

fst :: Lambda k => k (x * y) x
fst = kappa undefined $ \x -> x . unit

snd :: Lambda k => k (x * y) y
snd = kappa undefined $ \x -> id
