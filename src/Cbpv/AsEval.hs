{-# LANGUAGE DataKinds #-}
-- Strictness isn't any sort of optimization, just to show that the
-- semantics aren't reliant on Haskell's
{-# LANGUAGE StrictData #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cbpv.AsEval (reify, Action, Data) where

import Cbpv
import qualified Cbpv.Hom as Hom
import Data.Word
import Cbpv.Sort
import qualified Ccc.Type as Ccc
import qualified Ccc as Ccc
import qualified Lam.Type as Lam
import Prelude hiding ((.), id)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable ((:~:) (..))

reify :: Hom.Closed (U (F Unit)) (U (F U64)) -> Word64
reify x = go (Hom.fold x)

go :: Prog (U (F Unit)) (U (F U64)) -> Word64
go (C f) = case f (Thunk $ \w -> Unit :& w) of
  Thunk t -> case t (Effect 0) of
    (U64 y :& _) -> y

data family Prog (a :: Sort t) (b :: Sort t)
newtype instance Prog (a :: Sort SetTag) (b :: Sort SetTag) = C (Data a -> Data b)
newtype instance Prog (a :: Sort AlgebraTag) (b :: Sort AlgebraTag) = S (Action a -> Action b)

data family Data (a :: Set)

data instance Data (U a) = Thunk (Action Empty -> Action a)

data instance Data Unit = Unit
data instance Data (a * b) = Pair { firstOf :: (Data a), secondOf :: (Data b) }
newtype instance Data U64 = U64 Word64

-- | Actions are CBPVs computations but we use a different name for brevity
data family Action (a :: Algebra)
data instance Action Empty = Effect Int
data instance Action (a & b) = Data a :& Action b
infixr 9 :&
newtype instance Action (a ~> b) = Lam (Data a -> Action b)

instance Category (Prog @SetTag) where
  id = C $ \x -> x
  C f . C g = C (\x -> f (g x))

instance Category (Prog @AlgebraTag) where
  id = S $ \x -> x
  S f . S g = S (\x -> f (g x))

instance Code Prog where
  unit = C $ const Unit
  lift (C x) = C $ \env -> Pair (x Unit) env
  kappa f = C $ \(Pair h t) -> case f (C $ const h) of
    C y -> y t

instance Stack Prog where

instance Cbpv Prog Prog where
  thunk f = C $ \x -> Thunk $ \w -> case f (C $ \Unit -> x) of
    S y -> y w
  force (C x) = S $ \w -> case x Unit of
    Thunk t -> t w

  pass (C x) = S $ \(Lam f) -> f (x Unit)
  zeta f = S $ \env -> Lam $ \x -> case f (C $ const x) of
    S y -> y env

  push (C x) = S $ \env -> x Unit :& env
  pop f = S $ \(h :& t) -> case f (C $ const h) of
    S y -> y t

  u64 x = C $ const (U64 x)
  constant = constant' Lam.inferT
  cccIntrinsic x = case x of
     Ccc.AddIntrinsic -> undefined
  cbpvIntrinsic x = case x of
     AddIntrinsic -> addCbpvImpl
     MulIntrinsic -> mulCbpvImpl

constant' :: Lam.ST a -> String -> String -> Prog (F Unit) (AsAlgebra (Ccc.AsObject a))
constant' t pkg name = case maybeK t pkg name of
  Nothing -> undefined
  Just x -> x

maybeK :: Lam.ST a -> String -> String -> Maybe (Prog (F Unit) (AsAlgebra (Ccc.AsObject a)))
maybeK t pkgName name = do
  pkg <- Map.lookup pkgName constants
  Constant t' k <- Map.lookup name pkg
  Refl <- Lam.eqT t t'
  pure k

addCbpvImpl :: Prog (U64 * U64) U64
addCbpvImpl = C $ \(Pair (U64 x) (U64 y)) -> U64 (x + y)

mulCbpvImpl :: Prog (U64 * U64) U64
mulCbpvImpl = C $ \(Pair (U64 x) (U64 y)) -> U64 (x * y)

data Constant = forall a. Constant (Lam.ST a) (Prog (F Unit) (AsAlgebra (Ccc.AsObject a)))

constants :: Map String (Map String Constant)
constants = Map.fromList [
  ("core", Map.fromList [
      ("add", Constant Lam.inferT addImpl),
      ("multiply", Constant Lam.inferT multiplyImpl),
      ("subtract", Constant Lam.inferT subtractImpl)
      ])
  ]

addImpl :: Prog (F Unit) (AsAlgebra (Ccc.AsObject (Lam.U64 Lam.~> Lam.U64 Lam.~> Lam.U64)))
addImpl = S $ \(Unit :& w0) ->
              Lam $ \(Thunk x) -> Lam $ \(Thunk y) -> case x w0 of
                 U64 x' :& w1 -> case y w1 of
                   U64 y' :& w2 -> U64 (x' + y') :& w2

multiplyImpl :: Prog (F Unit) (AsAlgebra (Ccc.AsObject (Lam.U64 Lam.~> Lam.U64 Lam.~> Lam.U64)))
multiplyImpl = S $ \(Unit :& w0) ->
              Lam $ \(Thunk x) -> Lam $ \(Thunk y) -> case x w0 of
                 U64 x' :& w1 -> case y w1 of
                   U64 y' :& w2 -> U64 (x' * y') :& w2

subtractImpl :: Prog (F Unit) (AsAlgebra (Ccc.AsObject (Lam.U64 Lam.~> Lam.U64 Lam.~> Lam.U64)))
subtractImpl = S $ \(Unit :& w0) ->
              Lam $ \(Thunk x) -> Lam $ \(Thunk y) -> case x w0 of
                 U64 x' :& w1 -> case y w1 of
                   U64 y' :& w2 -> U64 (x' - y') :& w2
