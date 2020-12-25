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
import Lam.Type
import Prelude hiding ((<*>))

main :: IO ()
main = do
  putStrLn "The Program"
  putStrLn (show program)

  putStrLn ""
  putStrLn "Kappa/Zeta Decomposition"
  putStrLn (show concrete)

  putStrLn ""
  putStrLn "Optimized Program"
  putStrLn (show optConcrete)

  putStrLn ""
  putStrLn "Cbpv Program"
  putStrLn (show cbpvConcrete)

  putStrLn ""
  putStrLn "Cbpv Optimized"
  putStrLn (show optCbpvConcrete)

  putStrLn ""
  putStrLn "Result"
  putStrLn (show result)

type TYPE = U64

program :: Lam.Closed TYPE
program =
  Lam.Closed $
    u64 3 `letBe` \z ->
      add <*> z <*> z

compiled :: Ccc k => k Ccc.Type.Unit (Ccc.Type.AsObject TYPE)
compiled = AsCcc.asCcc program

concrete :: Ccc.Closed Ccc.Type.Unit (Ccc.Type.AsObject TYPE)
concrete = Ccc.Closed compiled

optConcrete :: Ccc.Closed Ccc.Type.Unit (Ccc.Type.AsObject TYPE)
optConcrete = Ccc.Closed optimized

optimized :: Ccc k => k Ccc.Type.Unit (Ccc.Type.AsObject TYPE)
optimized = opt compiled

cbpv :: Cbpv c d => d (Cbpv.Sort.U (Cbpv.Sort.F Cbpv.Sort.Unit)) (Cbpv.Sort.U (AsAlgebra ((Ccc.Type.AsObject TYPE))))
cbpv = toCbpv optConcrete

cbpvConcrete :: Cbpv.Closed (Cbpv.Sort.U (Cbpv.Sort.F Cbpv.Sort.Unit)) (Cbpv.Sort.U (AsAlgebra ((Ccc.Type.AsObject TYPE))))
cbpvConcrete = Cbpv.Closed cbpv

optCbpv :: Cbpv c d => d (Cbpv.Sort.U (Cbpv.Sort.F Cbpv.Sort.Unit)) (Cbpv.Sort.U (AsAlgebra ((Ccc.Type.AsObject TYPE))))
optCbpv = AsOpt.opt cbpv

optCbpvConcrete :: Cbpv.Closed (Cbpv.Sort.U (Cbpv.Sort.F Cbpv.Sort.Unit)) (Cbpv.Sort.U (AsAlgebra ((Ccc.Type.AsObject TYPE))))
optCbpvConcrete = Cbpv.Closed optCbpv

result :: Word64
result = AsEval.reify optCbpv
