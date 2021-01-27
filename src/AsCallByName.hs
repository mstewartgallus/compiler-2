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

toCbpv :: Ccc.Term hom => hom a b -> Closed (U (AsAlgebra a)) (U (AsAlgebra b))
toCbpv x = Closed (go (Ccc.foldTerm x))

newtype V k a b = V {go :: Hom k (U (AsAlgebra a)) (U (AsAlgebra b))}

instance Ccc.Ccc (V k) where
  id = id' Ccc.inferT
  (.) = compose Ccc.inferT Ccc.inferT Ccc.inferT

  unit = unit' Ccc.inferT

  lift = lift' Ccc.inferT Ccc.inferT

  pass = pass' Ccc.inferT Ccc.inferT
  zeta = zeta' Ccc.inferT Ccc.inferT Ccc.inferT

  u64 n = V $ (thunk (\_ -> push (u64 n)))
  constant = constant' Lam.inferT
  cccIntrinsic = cccIntrinsic' Ccc.inferT Ccc.inferT

id' :: AlgebraOf a -> V k a a
id' (AlgebraOf Dict) = V id

compose :: AlgebraOf a -> AlgebraOf b -> AlgebraOf c -> V k b c -> V k a b -> V k a c
compose (AlgebraOf Dict) (AlgebraOf Dict) (AlgebraOf Dict) (V f) (V g) = V (f . g)

unit' :: AlgebraOf a -> V k a Ccc.Unit
unit' (AlgebraOf Dict) = V (thunk (\_ -> push unit))

lift' :: AlgebraOf a -> AlgebraOf b -> V k Ccc.Unit a -> V k b (a Ccc.* b)
lift' (AlgebraOf Dict) (AlgebraOf Dict) (V x) =
  V
    ( thunk $ \env ->
        push ((x . thunk (\_ -> push unit)) &&& env)
    )

pass' :: AlgebraOf a -> AlgebraOf b -> V k Ccc.Unit a -> V k (a Ccc.~> b) b
pass' (AlgebraOf Dict) (AlgebraOf Dict) (V x) = V $ thunk (\env -> pass (x . thunk (\_ -> push unit)) <<< force env)

zeta' :: AlgebraOf a -> AlgebraOf b -> AlgebraOf c -> (V k Ccc.Unit a -> V k b c) -> V k b (a Ccc.~> c)
zeta' (AlgebraOf Dict) (AlgebraOf Dict) (AlgebraOf Dict) f = V $
  thunk $ \env ->
    zeta $ \x ->
      force (go (f (V (x . unit))) . env)

cccIntrinsic' :: (Ccc.KnownT a, Ccc.KnownT b) => AlgebraOf a -> AlgebraOf b -> Ccc.Intrinsic a b -> V k a b
cccIntrinsic' (AlgebraOf Dict) (AlgebraOf Dict) intrins = V $ thunk (\x -> cccIntrinsic intrins <<< force x)

constant' :: Lam.KnownT a => Ccc.ObjectOf a -> String -> String -> V k Ccc.Unit (Ccc.AsObject a)
constant' (Ccc.ObjectOf Dict) = constant'' Ccc.inferT

constant'' :: Lam.KnownT a => AlgebraOf (Ccc.AsObject a) -> String -> String -> V k Ccc.Unit (Ccc.AsObject a)
constant'' (AlgebraOf Dict) pkg name = V (constant pkg name . unit)
