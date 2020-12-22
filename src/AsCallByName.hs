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
import qualified Lambda.HasUnit as Lambda
import qualified Lambda.Type as Lambda
import Prelude hiding (curry, id, return, uncurry, (.), (<*>))

newtype Expr c a b = E (c (U (AsAlgebra a)) (U (AsAlgebra b)))

toCbpv :: Cbpv c d => Expr d Lambda.Unit a -> d (U (F Unit)) (U (AsAlgebra a))
toCbpv (E x) = x

instance Cbpv c d => Category (Expr d) where
  id = E id
  E f . E g = E (f . g)

instance Cbpv c d => Lambda.HasUnit (Expr d) where
  unit = E (thunk (return unit))

instance Cbpv c d => Product.HasProduct (Expr d) where
  lift (E x) = E $ thunk (dolift (x . thunk (return unit)))
  kappa t f =
    E $
      thunk $
        ( pop (SU (asAlgebra t)) $ \x -> case f (E (x . unit)) of
            E y -> force y
        )
          . force id

dolift ::
  Cbpv c d =>
  d Unit (U a) ->
  c
    (F (U b))
    (U a & (U b & Empty))
dolift a = pop undefined $ \b ->
  push b
    >>> push a

instance Cbpv c d => Sum.HasSum (Expr d) where
  absurd = E (thunk (force absurd . force id))

  left = E (thunk (return left))
  right = E (thunk (return right))
  E f ||| E g = E (thunk (force (f ||| g) . force id))

instance Cbpv c d => Exp.HasExp (Expr d) where
  zeta t f = E $
    thunk $
      zeta (SU (asAlgebra t)) $ \x -> case f (E (x . unit)) of
        E y -> force y
  pass (E x) = E $ thunk (pass (x . thunk (return unit)) . force id)

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
