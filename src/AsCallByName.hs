{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

module AsCallByName (Expr, toCbpv, AsAlgebra) where

import Cbpv
import Cbpv.Sort
import Control.Category
import qualified Lambda
import qualified Lambda.HasExp as Exp
import qualified Lambda.HasProduct as Product
import qualified Lambda.HasSum as Sum
import qualified Lambda.Type as Type
import Prelude hiding (curry, id, return, uncurry, (.), (<*>))

newtype Expr c a b = E (c (U (AsAlgebra a)) (U (AsAlgebra b)))

type family AsAlgebra a = r where
  AsAlgebra Type.Unit = F Unit
  AsAlgebra Type.Void = F Void
  AsAlgebra (a Type.* b) = F (U (AsAlgebra a) * U (AsAlgebra b))
  AsAlgebra (a Type.+ b) = F (U (AsAlgebra a) + U (AsAlgebra b))
  AsAlgebra (a Type.~> b) = U (AsAlgebra a) ~> AsAlgebra b
  AsAlgebra Type.U64 = F U64

toCbpv :: Cbpv c d => Expr d Type.Unit a -> d (U (F Unit)) (U (AsAlgebra a))
toCbpv (E x) = x

instance Cbpv c d => Category (Expr d) where
  id = E id
  E f . E g = E (f . g)

instance Cbpv c d => Product.HasProduct (Expr d) where
  unit = E (thunk (return unit))

  first = E (thunk (force first . force id))
  second = E (thunk (force second . force id))
  E f &&& E g = E (thunk (return f `to` ((return g . return first) `to` return ((second . first) &&& second))))

instance Cbpv c d => Sum.HasSum (Expr d) where
  absurd = E (thunk (force absurd . force id))

  left = E (thunk (return left))
  right = E (thunk (return right))
  E f ||| E g = E (thunk (force id . force (thunk (return f) ||| thunk (return g)) . force id))

instance Cbpv c d => Exp.HasExp (Expr d) where
  curry (E f) = E (thunk (curry (force f . return (thunk id) . assocOut)))
  uncurry (E f) = E (thunk (uncurry (force f) . assocIn . force id))

instance Cbpv c d => Lambda.Lambda (Expr d) where
  u64 x = E (thunk (return (u64 x)))
  add = E (thunk (addLazy . force id))
