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
import Dict
import qualified Lam.Type as Lam
import Prelude hiding (fst, id, snd, (.))

toCbpv :: Ccc.Closed Ccc.Unit a -> Closed (U (F Unit)) (U (AsAlgebra a))
toCbpv x = Closed (go (Ccc.fold x))

newtype V k a b = V {go :: Hom k (U (AsAlgebra a)) (U (AsAlgebra b))}

instance Ccc.Ccc (V k) where
  id = id' Ccc.inferT
  (.) = compose Ccc.inferT Ccc.inferT Ccc.inferT

  unit = unit' Ccc.inferT

  lift = lift' Ccc.inferT Ccc.inferT Ccc.inferT

  pass = pass' Ccc.inferT Ccc.inferT Ccc.inferT
  zeta = zeta' Ccc.inferT Ccc.inferT Ccc.inferT

  u64 n = V $ (thunk (\_ -> lift (u64 n)))
  constant = constant' Lam.inferT
  cccIntrinsic = cccIntrinsic' Ccc.inferT Ccc.inferT

id' :: Ccc.ST a -> V k a a
id' t = case toKnownSort (asAlgebra t) of
  Dict -> V id

compose :: Ccc.ST a -> Ccc.ST b -> Ccc.ST c -> V k b c -> V k a b -> V k a c
compose a b c (V f) (V g) = case (toKnownSort (asAlgebra a), toKnownSort (asAlgebra b), toKnownSort (asAlgebra c)) of
  (Dict, Dict, Dict) -> V (f . g)

unit' :: Ccc.ST a -> V k a Ccc.Unit
unit' a = case toKnownSort (asAlgebra a) of
  Dict -> V (thunk (\_ -> lift unit))

lift' :: Ccc.ST a -> Ccc.ST b -> Ccc.ST c -> V k (a Ccc.* b) c -> V k Ccc.Unit a -> V k b c
lift' a b c (V f) (V x) = case (toKnownSort (asAlgebra a), toKnownSort (asAlgebra b), toKnownSort (asAlgebra c)) of
  (Dict, Dict, Dict) ->
    V $
      f
        . ( thunk $ \env ->
              lift ((x . thunk (\_ -> lift unit)) &&& env)
          )

pass' :: Ccc.ST a -> Ccc.ST b -> Ccc.ST c -> V k b (a Ccc.~> c) -> V k Ccc.Unit a -> V k b c
pass' a b c (V f) (V x) = case (toKnownSort (asAlgebra a), toKnownSort (asAlgebra b), toKnownSort (asAlgebra c)) of
  (Dict, Dict, Dict) -> V $ thunk (\env -> pass (x . thunk (\_ -> lift unit)) . force (f . env))

zeta' :: Ccc.ST a -> Ccc.ST b -> Ccc.ST c -> (V k Ccc.Unit a -> V k b c) -> V k b (a Ccc.~> c)
zeta' a b c f = case (toKnownSort (asAlgebra a), toKnownSort (asAlgebra b), toKnownSort (asAlgebra c)) of
  (Dict, Dict, Dict) -> V $
    thunk $ \env ->
      zeta $ \x ->
        force (go (f (V (x . unit))) . env)

cccIntrinsic' :: (Ccc.KnownT a, Ccc.KnownT b) => Ccc.ST a -> Ccc.ST b -> Ccc.Intrinsic a b -> V k a b
cccIntrinsic' a b intrins = case (toKnownSort (asAlgebra a), toKnownSort (asAlgebra b)) of
  (Dict, Dict) -> V $ thunk (\x -> cccIntrinsic intrins . force x)

constant' :: Lam.KnownT a => Lam.ST a -> String -> String -> V k Ccc.Unit (Ccc.AsObject a)
constant' t pkg name = case toKnownSort (asAlgebra (Ccc.asObject t)) of
  Dict -> V $ thunk (\_ -> constant pkg name . lift unit)
