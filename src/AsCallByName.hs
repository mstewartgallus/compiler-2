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
import qualified Ccc
import qualified Ccc.HasExp as Exp
import qualified Ccc.HasProduct as Product
import qualified Ccc.HasUnit as Ccc
import qualified Ccc.Type as Ccc
import Control.Category
import Prelude hiding (curry, id, return, uncurry, (.), (<*>))

newtype Expr c a b = E {unE :: c (U (AsAlgebra a)) (U (AsAlgebra b))}

toCbpv :: Cbpv c d => Expr d Ccc.Unit a -> d (U (F Unit)) (U (AsAlgebra a))
toCbpv (E x) = x

instance Cbpv c d => Category (Expr d) where
  id = E id
  E f . E g = E (f . g)

instance Cbpv c d => Ccc.HasUnit (Expr d) where
  unit = E $ (pip . unit)

pip :: Cbpv c d => d Unit (U (F Unit))
pip = thunk id

instance Cbpv c d => Product.HasProduct (Expr d) where
  lift (E x) =
    E $
      thunk
        ( pop undefined $ \b ->
            push b
              >>> push
                ( pip
                    >>> x
                )
        )

  kappa t f =
    E $
      thunk $
        force id
          >>> ( pop (SU (asAlgebra t)) $ \x ->
                  force $
                    unE $
                      f $
                        E
                          ( unit
                              >>> x
                          )
              )

instance Cbpv c d => Exp.HasExp (Expr d) where
  pass (E x) =
    E $
      thunk $
        force id
          >>> pass
            ( pip
                >>> x
            )

  zeta t f = E $
    thunk $
      zeta (SU (asAlgebra t)) $ \x ->
        force $
          unE $
            f $
              E
                ( unit
                    >>> x
                )

instance Cbpv c d => Ccc.Ccc (Expr d) where
  u64 x =
    E $
      thunk $
        force id
          >>> ( pop undefined $ \env ->
                  push (u64 x . env)
              )
  constant t pkg name = E (thunk (constant t pkg name . force id))
  cccIntrinsic x = E (cccIntrinsic x)
