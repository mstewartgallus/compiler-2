{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

module AsCallByName (Expr, toCbpv) where

import Cbpv
import Cbpv.Sort
import Control.Category
import qualified Lambda
import qualified Lambda.HasExp as Exp
import qualified Lambda.HasLet as Let
import qualified Lambda.HasProduct as Product
import qualified Lambda.HasSum as Sum
import qualified Lambda.Type as Lambda
import Prelude hiding (curry, id, return, uncurry, (.), (<*>))

newtype Expr c a b = E (c (U (AsAlgebra a)) (U (AsAlgebra b)))

toCbpv :: Cbpv c d => Expr d Lambda.Unit a -> d (U (F Unit)) (U (AsAlgebra a))
toCbpv (E x) = x

instance Cbpv c d => Category (Expr d) where
  id = E id
  E f . E g = E (f . g)

instance Cbpv c d => Product.HasProduct (Expr d) where
  unit = E (thunk (return unit))

  first = E (thunk (force first . force id))
  second = E (thunk (force second . force id))
  E f &&& E g = E (thunk (return (f &&& g)))

instance Cbpv c d => Sum.HasSum (Expr d) where
  absurd = E (thunk (force absurd . force id))

  left = E (thunk (return left))
  right = E (thunk (return right))
  E f ||| E g = E (thunk (force (f ||| g) . force id))

instance Cbpv c d => Exp.HasExp (Expr d) where
  curry (E f) = E (thunk (curry (force f . return (thunk id) . pop)))
  uncurry (E f) = E (thunk (uncurry (force f) . push . force id))

instance Cbpv c d => Let.HasLet (Expr d) where
  be t (E x) f =
    E $
      ( x `be` \x' -> case f (E (x' . unit)) of
          E y -> y
      )

instance Cbpv c d => Lambda.Lambda (Expr d) where
  u64 x = E (thunk (return (u64 x) . force id))
  constant t pkg name = E (thunk (constant t pkg name . force id))
  lambdaIntrinsic x = E (lambdaIntrinsic x)
