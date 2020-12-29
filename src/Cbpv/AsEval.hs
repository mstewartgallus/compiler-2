{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Cbpv.AsEval (reify, Action, Data) where

import Cbpv
import qualified Cbpv.Hom as Hom
import Control.Category
import Data.Word
import Cbpv.Sort
import qualified Ccc.Type as Ccc
import qualified Ccc as Ccc
import qualified Lam.Type as Lam
import Prelude hiding ((.), id)

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
  id = C id
  C f . C g = C (f . g)

instance Category (Prog @AlgebraTag) where
  id = S id
  S f . S g = S (f . g)

instance Code Prog where
  unit = C $ const Unit
  fst = C $ \(Pair x _) -> x
  snd = C $ \(Pair _ x) -> x
  C x &&& C y = C $ \env -> Pair (x env) (y env)

instance Stack Prog where

instance Cbpv Prog Prog where
  thunk _ f = C $ \x -> Thunk $ \w -> case f (C $ \Unit -> x) of
    S y -> y w
  force (C f) (C x) = S $ \w -> case f (x Unit) of
    Thunk t -> t w

  pass (C x) = S $ \(Lam f) -> f (x Unit)
  zeta _ f = S $ \env -> Lam $ \x -> case f (C $ const x) of
    S y -> y env

  lift (C x) = S $ \y -> x Unit :& y
  pop _ f = S $ \(h :& t) -> case f (C $ const h) of
    S y -> y t

  u64 x = C $ const (U64 x)
  constant t pkg name = case (t, pkg, name) of
     (Lam.SU64 Lam.:-> (Lam.SU64 Lam.:-> Lam.SU64), "core", "add") -> addImpl
  cccIntrinsic x = case x of
     Ccc.AddIntrinsic -> addCccImpl
  cbpvIntrinsic x = case x of
     AddIntrinsic -> addCbpvImpl

addImpl :: Prog (F Unit) (AsAlgebra (Ccc.AsObject (Lam.U64 Lam.~> Lam.U64 Lam.~> Lam.U64)))
addImpl = S $ \(Unit :& w0) ->
              Lam $ \(Thunk x) -> Lam $ \(Thunk y) -> case x w0 of
                 U64 x' :& w1 -> case y w1 of
                   U64 y' :& w2 -> U64 (x' + y') :& w2

addCccImpl :: Prog (U (AsAlgebra (Ccc.U64 Ccc.* Ccc.U64))) (U (AsAlgebra Ccc.U64))
addCccImpl = C $ \(Thunk input) -> undefined

addCbpvImpl :: Prog (U64 * U64) U64
addCbpvImpl = C $ \(Pair (U64 x) (U64 y)) -> U64 (x + y)
