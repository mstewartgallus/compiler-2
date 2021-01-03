{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module AsPointed (asPointed) where

import Cbpv
import Cbpv.Hom
import Cbpv.Sort
import qualified Ccc.Type as Ccc
import Control.Monad.State hiding (lift)
import Data.Kind
import Data.Typeable ((:~:) (..))
import Dict
import qualified Lam.Type as Lam
import qualified Pointless as Pointless
import qualified Pointless.Hom as Pointless
import Prelude hiding (curry, drop, fst, id, snd, uncurry, (.))

asPointed :: Pointless.Hom a b -> Closed @SetTag a b
asPointed x = Closed $ case Pointless.fold x of
  C y -> y

newtype C (f :: Algebra -> Algebra -> Type) (g :: Set -> Set -> Type) a b = C (g a b)

newtype K (f :: Algebra -> Algebra -> Type) (g :: Set -> Set -> Type) a b = K (f a b)

instance Cbpv f g => Category (C f g) where
  id = C id
  C f . C g = C (f . g)

instance Cbpv f g => Category (K f g) where
  id = K id
  K f . K g = K (f . g)

instance Cbpv f g => Pointless.Stack (K f g)

instance Cbpv f g => Pointless.Code (C f g) where
  unit = C unit
  fst = C fst
  snd = C snd
  C x &&& C y = C (x &&& y)

instance Cbpv f g => Pointless.Pointless (K f g) (C f g) where
  uncurry (K f) = K (pop (\x -> pass x . f))
  force (C x) = K (pop (\env -> force (x . env)))

  thunk (K x) = C (thunk $ \env -> x . push env)
  inStack = K (push unit)
  drop = K (pop (\_ -> id))
  lmapStack (C f) = K (pop (\x -> push (f . x)))
  rmapStack (K f) = K (pop (\x -> push x . f))

  push = K $
    pop $ \x ->
      push (fst . x)
        . push (snd . x)
  pop = K $
    pop $ \x ->
      pop $ \y ->
        push (x &&& y)

  u64 n = C (u64 n)
  constant pkg name = C (constant pkg name)
  cbpvIntrinsic x = C (cbpvIntrinsic x)
