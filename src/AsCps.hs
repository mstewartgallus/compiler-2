{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module AsCps where

import qualified Cbpv
import qualified Cbpv.Hom as Cbpv
import qualified Cbpv.Sort as Cbpv
import Cps
import Cps.Sort
import Data.Kind
import Dict
import qualified Lam.Type as Lam
import Prelude hiding (fst, id, snd, (.))

-- toCps :: Cbpv.Term hom => hom a b -> Closed (SetAsCps a) (SetAsCps b)
-- toCps x = Closed (go (Cbpv.foldCode x))

newtype VS (f :: Algebra -> Algebra -> Type) (g :: Set -> Set -> Type) a b = VS (g (SetAsCps b) (SetAsCps a))

newtype VA (f :: Algebra -> Algebra -> Type) (g :: Set -> Set -> Type) a b = VA (f (AlgAsCps b) (AlgAsCps a))

instance Cps f g => Cbpv.Code (VS f g) where
  id = id' Cbpv.inferSet
  (.) = compose Cbpv.inferSet Cbpv.inferSet Cbpv.inferSet

instance Cps f g => Cbpv.Stack (VA f g) where
  skip = skip' Cbpv.inferAlgebra
  (<<<) = kcompose Cbpv.inferAlgebra Cbpv.inferAlgebra Cbpv.inferAlgebra

instance Cps f g => Cbpv.Cbpv (VA f g) (VS f g) where
  push = push' Cbpv.inferSet Cbpv.inferAlgebra
  pop = pop' Cbpv.inferSet Cbpv.inferAlgebra Cbpv.inferAlgebra

  pass = pass' Cbpv.inferSet Cbpv.inferAlgebra
  zeta = zeta' Cbpv.inferSet Cbpv.inferAlgebra Cbpv.inferAlgebra

--   u64 n = V $ (thunk (\_ -> push (u64 n)))
--   -- constant = constant' Lam.inferSet
--   -- cccIntrinsic = cccIntrinsic' Cbpv.inferSet Cbpv.inferSet

id' :: Cps f g => CpsOfSet a -> VS f g a a
id' (CpsOfSet Dict) = VS Cps.id

compose :: Cps f g => CpsOfSet a -> CpsOfSet b -> CpsOfSet c -> VS f g b c -> VS f g a b -> VS f g a c
compose (CpsOfSet Dict) (CpsOfSet Dict) (CpsOfSet Dict) (VS f) (VS g) = VS (g . f)

skip' :: Cps f g => CpsOfAlg a -> VA f g a a
skip' (CpsOfAlg Dict) = VA Cps.skip

kcompose :: Cps f g => CpsOfAlg a -> CpsOfAlg b -> CpsOfAlg c -> VA f g b c -> VA f g a b -> VA f g a c
kcompose (CpsOfAlg Dict) (CpsOfAlg Dict) (CpsOfAlg Dict) (VA f) (VA g) = VA (g <<< f)

push' :: Cps f g => CpsOfSet a -> CpsOfAlg b -> VS f g Cbpv.Unit a -> VA f g b (a Cbpv.& b)
push' (CpsOfSet Dict) (CpsOfAlg Dict) (VS x) = VA (copush x)

pop' :: Cps f g => CpsOfSet a -> CpsOfAlg b -> CpsOfAlg c -> (VS f g Cbpv.Unit a -> VA f g b c) -> VA f g (a Cbpv.& b) c
pop' (CpsOfSet Dict) (CpsOfAlg Dict) (CpsOfAlg Dict) f = VA $
  copop $ \x ->
    case f (VS x) of
      VA y -> y

pass' :: Cps f g => CpsOfSet a -> CpsOfAlg b -> VS f g Cbpv.Unit a -> VA f g (a Cbpv.~> b) b
pass' (CpsOfSet Dict) (CpsOfAlg Dict) (VS x) = VA (copass x)

zeta' :: Cps f g => CpsOfSet a -> CpsOfAlg b -> CpsOfAlg c -> (VS f g Cbpv.Unit a -> VA f g b c) -> VA f g b (a Cbpv.~> c)
zeta' (CpsOfSet Dict) (CpsOfAlg Dict) (CpsOfAlg Dict) f = VA $
  cozeta $ \x ->
    case f (VS x) of
      VA y -> y
