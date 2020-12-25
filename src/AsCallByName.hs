{-# LANGUAGE GADTs #-}

module AsCallByName (toCbpv) where

import Cbpv
import Cbpv.Hom
import Cbpv.Sort
import qualified Ccc
import qualified Ccc.HasExp as Ccc
import qualified Ccc.HasProduct as Ccc
import qualified Ccc.HasUnit as Ccc
import qualified Ccc.Hom as Ccc
import qualified Ccc.Type as Ccc
import Control.Category
import Prelude hiding (id, (.))

toCbpv :: Ccc.Closed Ccc.Unit a -> Closed (U (F Unit)) (U (AsAlgebra a))
toCbpv (Ccc.Closed x) = Closed (go x)

go :: Cbpv c d => Ccc.Hom (V d) a b -> d (U (AsAlgebra a)) (U (AsAlgebra b))
go x = case x of
  Ccc.Var (V h) -> h
  Ccc.Id -> id
  f Ccc.:.: g -> go f . go g
  Ccc.UnitHom -> pip . unit
  Ccc.Lift x ->
    let x' = go x
     in thunk $ pop undefined $ \y -> push (lift (x' . pip) . y)
  Ccc.Pass x ->
    thunk $ force id >>> pass (pip >>> go x)
  Ccc.Zeta t f -> thunk $
    zeta (SU (asAlgebra t)) $ \x ->
      force $
        go $ f (V (unit >>> x))
  Ccc.U64 n -> thunk (pop inferSort $ \_ -> push (u64 n))
  Ccc.Constant t pkg name -> thunk (force id >>> constant t pkg name)
  Ccc.CccIntrinsic x -> cccIntrinsic x

pip :: Cbpv c d => d Unit (U (F Unit))
pip = thunk id

newtype V d a b = V (d (U (AsAlgebra a)) (U (AsAlgebra b)))
