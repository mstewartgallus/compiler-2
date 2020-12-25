{-# LANGUAGE DataKinds #-}

module Main where

import AsCallByName
import qualified AsCcc
import Cbpv (Cbpv)
import qualified Cbpv.AsEval as AsEval
import qualified Cbpv.AsOpt as AsOpt
import qualified Cbpv.Hom as Cbpv
import Cbpv.Sort (AsAlgebra)
import qualified Cbpv.Sort
import Ccc (Ccc)
import Ccc.AsOpt
import qualified Ccc.Hom as Ccc
import qualified Ccc.Type
import Data.Word
import Lam
import qualified Lam.Term as Lam
import Lam.Type
import Prelude hiding ((<*>))

main :: IO ()
main = do
  putStrLn "The Program"
  putStrLn (show program)

  putStrLn ""
  putStrLn "Kappa/Zeta Decomposition"
  putStrLn (show compiled)

  putStrLn ""
  putStrLn "Optimized Program"
  putStrLn (show optimized)

  putStrLn ""
  putStrLn "Cbpv Program"
  putStrLn (show cbpv)

  putStrLn ""
  putStrLn "Cbpv Optimized"
  putStrLn (show optCbpv)

  putStrLn ""
  putStrLn "Result"
  putStrLn (show result)

type TYPE = U64

program :: Lam.Closed TYPE
program =
  Lam.Closed $
    u64 3 `letBe` \z ->
      add <*> z <*> z

compiled :: Ccc.Closed Ccc.Type.Unit (Ccc.Type.AsObject TYPE)
compiled = AsCcc.asCcc program

optimized :: Ccc.Closed Ccc.Type.Unit (Ccc.Type.AsObject TYPE)
optimized = opt compiled

cbpv :: Cbpv.Closed (Cbpv.Sort.U (Cbpv.Sort.F Cbpv.Sort.Unit)) (Cbpv.Sort.U (AsAlgebra ((Ccc.Type.AsObject TYPE))))
cbpv = toCbpv optimized

optCbpv :: Cbpv.Closed (Cbpv.Sort.U (Cbpv.Sort.F Cbpv.Sort.Unit)) (Cbpv.Sort.U (AsAlgebra ((Ccc.Type.AsObject TYPE))))
optCbpv = AsOpt.opt cbpv

result :: Word64
result = AsEval.reify (Cbpv.abstract optCbpv)
