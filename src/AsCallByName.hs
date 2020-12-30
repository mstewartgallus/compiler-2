{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module AsCallByName (toCbpv) where

import Cbpv
import Cbpv.Hom
import Cbpv.Sort
import qualified Ccc
import qualified Ccc.Hom as Ccc
import qualified Ccc.Type as Ccc
import Control.Category
import qualified Lam.Type as Lam
import Prelude hiding (fst, id, snd, (.))

toCbpv :: Ccc.Closed Ccc.Unit a -> Closed (U (F Unit)) (U (AsAlgebra a))
toCbpv x = Closed (go (Ccc.fold x))

newtype V k a b = V {go :: Hom k (U (AsAlgebra a)) (U (AsAlgebra b))}

instance Ccc.Ccc (V k) where
  id = V id
  V f . V g = V (f . g)

  unit = V (thunk inferSort (\_ -> lift unit) . unit)

  lift (V x) = V $
    thunk undefined $ \env ->
      lift ((x . thunk inferSort (\_ -> lift unit) . unit) &&& env)

  pass (V x) = V $ thunk undefined (\env -> pass (x . thunk inferSort (\_ -> lift unit)) . force env)
  zeta f =
    let t = argOf f
     in V $
          thunk undefined $ \env ->
            zeta (SU (asAlgebra t)) $ \x ->
              force (go (f (V (x . unit))) . env)

  u64 n = V $ (thunk inferSort (\_ -> lift (u64 n)) . unit)
  constant pkg name = V $ thunk inferSort (\_ -> constant undefined pkg name . lift unit)
  cccIntrinsic x = V $ cccIntrinsic x

argOf :: Ccc.KnownT a => (V k Ccc.Unit a -> V k b c) -> Ccc.ST a
argOf _ = Ccc.inferT
