{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

-- | Remove duplicate force/thunk pairs
module Cbpv.AsOpt (Stack, Code, opt) where

import Cbpv
import qualified Cbpv.AsRepeat as AsRepeat
import Control.Category
import Cbpv.Sort
import qualified Lambda.Type as Lambda
import Prelude hiding ((.), id, curry, uncurry, Monad (..))

newtype Stack f g a b = K (AsRepeat.Stack f g a b)
newtype Code f g a b = C (AsRepeat.Code f g a b)

opt :: Code f g a b -> g a b
opt (C x) = AsRepeat.repeat 20 x

instance (Category f, Category g) => Category (Stack f g) where
  id = K id
  K f . K g = K (f . g)

instance (Category f, Category g) => Category (Code f g) where
  id = C id
  C f . C g = C (f . g)

instance Cbpv f g => Cbpv (Stack f g) (Code f g) where
  thunk (K f) = C (thunk f)
  force (C f) = K (force f)

  return (C f) = K (return f)

  unit = C unit
  C f &&& C g = C (f &&& g)
  first = C first
  second = C second

  absurd = C absurd
  C f ||| C g = C (f ||| g)
  left = C left
  right = C right

  pop = K pop
  push = K push

  uncurry (K f) = K (uncurry f)
  curry (K f) = K (curry f)

  u64 x = C (u64 x)

  constant t pkg name = K (constant t pkg name)
  lambdaConstant t pkg name = K $ case (t, pkg, name) of
    (Lambda.SU64 Lambda.:-> (Lambda.SU64 Lambda.:-> Lambda.SU64), pkg, name) -> addIntrinsic
    _ -> lambdaConstant t pkg name

-- | fixme.. cleanup this mess
addIntrinsic :: Cbpv stack code => stack (F Unit) (AsAlgebra (Lambda.U64 Lambda.~> (Lambda.U64 Lambda.~> Lambda.U64)))
addIntrinsic = curry (
  pop
  >>> return first
  >>> force id
  >>> curry (
    pop
    >>> (push . return (second &&& first))
    >>> uncurry (
        force id
            >>> (push . return (id &&& unit))
            >>> uncurry add
            )
  )
  )
