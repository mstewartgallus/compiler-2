module AsCcc (AsCcc, asCcc) where

import Ccc
import Ccc.HasExp
import Ccc.HasProduct
import Ccc.Type
import Control.Category
import qualified Lam as Lam
import Prelude hiding (id, (.))

asCcc :: AsCcc k a -> k Unit (AsObject a)
asCcc (Pf x) = x

newtype AsCcc k a = Pf (k Unit (AsObject a))

instance Ccc k => Lam.Lam (AsCcc k) where
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
