module AsLambda (AsLambda, asLambda) where

import Control.Category
import qualified Hoas as Hoas
import Lambda
import Lambda.HasExp
import Lambda.HasProduct
import Lambda.Type
import Prelude hiding (id, (.))

asLambda :: AsLambda k a -> k Unit (AsObject a)
asLambda (Pf x) = x

newtype AsLambda k a = Pf (k Unit (AsObject a))

instance Lambda k => Hoas.Hoas (AsLambda k) where
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
