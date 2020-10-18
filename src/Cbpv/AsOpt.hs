{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

-- | Remove duplicate force/thunk pairs
module Cbpv.AsOpt (Stk, Cde, opt) where

import Cbpv
import qualified Cbpv.AsRepeat as AsRepeat
import Control.Category
import Cbpv.Sort
import qualified Lambda.Type as Lambda
import qualified Lambda as Lambda
import Prelude hiding ((.), id, curry, uncurry, Monad (..))

newtype Stk f g a b = K (AsRepeat.Stk f g a b)
newtype Cde f g a b = C (AsRepeat.Cde f g a b)

opt :: Cde f g a b -> g a b
opt (C x) = AsRepeat.repeat 100 x

instance (Category f, Category g) => Category (Stk f g) where
  id = K id
  K f . K g = K (f . g)

instance (Category f, Category g) => Category (Cde f g) where
  id = C id
  C f . C g = C (f . g)

instance Cbpv f g => Code (Cde f g) where
  unit = C unit
  C f &&& C g = C (f &&& g)
  first = C first
  second = C second

  absurd = C absurd
  C f ||| C g = C (f ||| g)
  left = C left
  right = C right

instance Cbpv f g => Stack (Stk f g) where
  pop = K pop
  push = K push

  uncurry (K f) = K (uncurry f)
  curry (K f) = K (curry f)

instance Cbpv f g => Cbpv (Stk f g) (Cde f g) where
  thunk (K f) = C (thunk f)
  force (C f) = K (force f)

  return (C f) = K (return f)

  be (C x) f = C $ be x $ \x' -> case f (C x') of
    C y -> y

  letTo (K x) f = K $ letTo x $ \x' -> case f (C x') of
    K y -> y

  u64 x = C (u64 x)

  constant t pkg name = K (constant t pkg name)

  lambdaIntrinsic x = C $ case x of
    Lambda.AddIntrinsic -> addIntrinsic
    _ -> lambdaIntrinsic x
  cbpvIntrinsic x = C (cbpvIntrinsic x)

-- | fixme.. cleanup this mess
addIntrinsic :: Cbpv stack code => code (U (AsAlgebra (Lambda.U64 Lambda.* Lambda.U64))) (U (AsAlgebra Lambda.U64))
addIntrinsic = thunk (doAdd . force id)

doAdd :: Cbpv stack code => stack (F (U (F U64) * U (F U64))) (F U64)
doAdd = uncurry (curry (uncurry (curry (return add . pop) . force id) . push . return (second &&& first) . pop) . force id) . push
