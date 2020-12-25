{-# LANGUAGE GADTs #-}

module AsCcc (asCcc) where

import Ccc
import Ccc.HasExp
import Ccc.HasProduct
import Ccc.Type
import Control.Category
import qualified Lam as Lam
import Prelude hiding (id, (.))

asCcc :: Ccc k => Lam.Closed a -> k Unit (AsObject a)
asCcc (Lam.Closed x) = go x

newtype V k a = V (k Unit (AsObject a))

go :: Ccc hom => Lam.Term (V hom) a -> hom Unit (AsObject a)
go x = case x of
  Lam.Var (V h) -> h
  Lam.App f x -> pass (go x) . go f
  Lam.Lam t f ->
    zeta (asObject t) $ \x ->
      go (f (V x))
  Lam.Be x t f ->
    lift (go x)
      >>> ( kappa (asObject t) $ \x' ->
              go (f (V x'))
          )
  Lam.U64 x -> u64 x
  Lam.Constant t pkg name -> constant t pkg name
