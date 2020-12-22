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
import Prelude hiding (curry, fst, id, snd, uncurry, (.), (<*>))

pointFree :: PointFree k a -> k Unit (AsObject a)
pointFree (Pf x) = x

newtype PointFree k a = Pf (k Unit (AsObject a))

instance Lambda k => Hoas.Hoas (PointFree k) where
  Pf f <*> Pf x = Pf (pass x . f)

  lam t f = Pf $
    zeta (asObject t) $ \x -> case f (Pf x) of
      Pf y -> y

  be (Pf x) t f =
    Pf $
      lift x
        >>> ( kappa (asObject t) $ \x' -> case f (Pf x') of
                Pf y -> y
            )

  u64 x = Pf (u64 x)
  constant t pkg name = Pf (constant t pkg name)

fst :: Lambda k => k (x * y) x
fst = kappa undefined $ \x -> x . unit

snd :: Lambda k => k (x * y) y
snd = kappa undefined $ \x -> id
