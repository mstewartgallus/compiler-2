{-# LANGUAGE DataKinds #-}

module Main where

import AsCallByName
import qualified AsCcc
import Cbpv (Cbpv)
import qualified Cbpv.AsEval as AsEval
import qualified Cbpv.AsOpt as AsOpt
import qualified Cbpv.AsView as AsViewCbpv
import Cbpv.Sort (AsAlgebra)
import qualified Cbpv.Sort
import Ccc (Ccc)
import Ccc.AsOpt
import Ccc.AsView
import qualified Ccc.Type
import Data.Word
import Lam
import qualified Lam.AsView as AsLamView
import Lam.Type
import Prelude hiding ((<*>))

main :: IO ()
main = do
  putStrLn "The Program"
  putStrLn (AsLamView.view program)

  putStrLn ""
  putStrLn "Kappa/Zeta Decomposition"
  putStrLn (view compiled)

  putStrLn ""
  putStrLn "Optimized Program"
  putStrLn (view optimized)

  putStrLn ""
  putStrLn "Cbpv Program"
  putStrLn (AsViewCbpv.view cbpv)

  putStrLn ""
  putStrLn "Cbpv Optimized"
  putStrLn (AsViewCbpv.view optCbpv)

  putStrLn ""
  putStrLn "Result"
  putStrLn (show result)

type TYPE = U64

program :: Lam t => t TYPE
program =
  u64 3 `letBe` \z ->
    add <*> z <*> z

compiled :: Ccc k => k Ccc.Type.Unit (Ccc.Type.AsObject TYPE)
compiled = AsCcc.asCcc program

optimized :: Ccc k => k Ccc.Type.Unit (Ccc.Type.AsObject TYPE)
optimized = opt compiled

cbpv :: Cbpv c d => d (Cbpv.Sort.U (Cbpv.Sort.F Cbpv.Sort.Unit)) (Cbpv.Sort.U (AsAlgebra ((Ccc.Type.AsObject TYPE))))
cbpv = toCbpv optimized

optCbpv :: Cbpv c d => d (Cbpv.Sort.U (Cbpv.Sort.F Cbpv.Sort.Unit)) (Cbpv.Sort.U (AsAlgebra ((Ccc.Type.AsObject TYPE))))
optCbpv = AsOpt.opt cbpv

result :: Word64
result = AsEval.reify optCbpv
