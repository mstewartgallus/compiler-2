{-# LANGUAGE DataKinds #-}

module Main where

import AsCallByName
import qualified AsLambda
import Cbpv (Cbpv)
import qualified Cbpv.AsEval as AsEval
import qualified Cbpv.AsOpt as AsOpt
import qualified Cbpv.AsView as AsViewCbpv
import Cbpv.Sort (AsAlgebra)
import qualified Cbpv.Sort
import Data.Word
import Hoas
import qualified Hoas.AsView as AsHoasView
import Hoas.Type
import Lambda (Lambda)
import Lambda.AsOpt
import Lambda.AsView
import qualified Lambda.Type
import Prelude hiding ((<*>))

main :: IO ()
main = do
  putStrLn "The Program"
  putStrLn (AsHoasView.view program)

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

program :: Hoas t => t TYPE
program =
  u64 3 `letBe` \z ->
    add <*> z <*> z

compiled :: Lambda k => k Lambda.Type.Unit (Lambda.Type.AsObject TYPE)
compiled = AsLambda.pointFree program

optimized :: Lambda k => k Lambda.Type.Unit (Lambda.Type.AsObject TYPE)
optimized = opt compiled

cbpv :: Cbpv c d => d (Cbpv.Sort.U (Cbpv.Sort.F Cbpv.Sort.Unit)) (Cbpv.Sort.U (AsAlgebra ((Lambda.Type.AsObject TYPE))))
cbpv = toCbpv optimized

optCbpv :: Cbpv c d => d (Cbpv.Sort.U (Cbpv.Sort.F Cbpv.Sort.Unit)) (Cbpv.Sort.U (AsAlgebra ((Lambda.Type.AsObject TYPE))))
optCbpv = AsOpt.opt cbpv

result :: Word64
result = AsEval.reify optCbpv
