{-# LANGUAGE GADTs #-}

module AsCallByName (toCbpv) where

import Cbpv
import Cbpv.Hom
import Cbpv.Sort
import qualified Ccc
import qualified Ccc.HasExp as Ccc
import qualified Ccc.HasProduct as Ccc
import qualified Ccc.HasUnit as Ccc
import qualified Ccc.Hom as Ccc
import qualified Ccc.Type as Ccc
import Control.Category
import Prelude hiding (id, (.))

toCbpv :: Ccc.Closed Ccc.Unit a -> Closed (U (F Unit)) (U (AsAlgebra a))
toCbpv x = Closed (go (Ccc.fold x))

newtype V k a b = V {go :: Hom k (U (AsAlgebra a)) (U (AsAlgebra b))}

instance Category (V k) where
  id = V id
  V f . V g = V (f . g)

instance Ccc.HasUnit (V k) where
  unit = V (pip . unit)

instance Ccc.HasProduct (V k) where
  lift (V x) = V $ thunk $ pop undefined $ \y -> push (lift (x . pip) . y)

instance Ccc.HasExp (V k) where
  pass (V x) = V $ thunk (force id >>> pass (pip >>> x))
  zeta t f = V $
    thunk $
      zeta (SU (asAlgebra t)) $ \x ->
        force $
          go $ f (V (unit >>> x))

instance Ccc.Ccc (V k) where
  u64 n = V $ thunk (pop inferSort $ \_ -> push (u64 n))
  constant t pkg name = V $ thunk (force id >>> constant t pkg name)
  cccIntrinsic x = V $ cccIntrinsic x

pip :: Hom k Unit (U (F Unit))
pip = thunk id
