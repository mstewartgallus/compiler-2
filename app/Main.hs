{-# LANGUAGE DataKinds #-}

module Main where

import AsCallByName
import qualified AsTerm
import Cbpv (Cbpv)
import qualified Cbpv.AsEval as AsEval
import qualified Cbpv.AsOpt as AsOpt
import qualified Cbpv.AsView as AsViewCbpv
import qualified Cbpv.Sort
import Data.Word
import Hoas
import Hoas.AsBound
import qualified Hoas.AsView as AsHoasView
import Hoas.Bound (Bound)
import Hoas.Type
import qualified Id
import Lambda (Lambda)
import Lambda.AsOptimized
import Lambda.AsView
import qualified Lambda.Type
import Prelude hiding ((<*>))

main :: IO ()
main = do
  x <- Id.stream

  putStrLn "The Program"
  putStrLn (AsHoasView.view (bound x))

  putStrLn ""
  putStrLn "Point-Free Program"
  putStrLn (view (compiled x))

  putStrLn ""
  putStrLn "Optimized Program"
  putStrLn (view (optimized x))

  putStrLn ""
  putStrLn "Cbpv Program"
  putStrLn (AsViewCbpv.view (cbpv x))

  putStrLn ""
  putStrLn "Cbpv Optimized"
  putStrLn (AsViewCbpv.view (optCbpv x))

  putStrLn ""
  putStrLn "Result"
  putStrLn (show (result x))

type TYPE = U64

program :: Hoas t => t Unit TYPE
program =
  u64 3 `letBe` \z ->
    add <*> z <*> z

bound :: Bound t => Id.Stream -> t Unit TYPE
bound str = bindPoints str program

compiled :: Lambda k => Id.Stream -> k Lambda.Type.Unit (AsTerm.AsObject TYPE)
compiled str = AsTerm.pointFree (bound str)

optimized :: Lambda k => Id.Stream -> k Lambda.Type.Unit (AsTerm.AsObject TYPE)
optimized str = optimize (compiled str)

cbpv :: Cbpv c d => Id.Stream -> d (Cbpv.Sort.U (Cbpv.Sort.F Cbpv.Sort.Unit)) (Cbpv.Sort.U (AsAlgebra ((AsTerm.AsObject TYPE))))
cbpv str = toCbpv (optimized str)

optCbpv :: Cbpv c d => Id.Stream -> d (Cbpv.Sort.U (Cbpv.Sort.F Cbpv.Sort.Unit)) (Cbpv.Sort.U (AsAlgebra ((AsTerm.AsObject TYPE))))
optCbpv str = AsOpt.opt (cbpv str)

result :: Id.Stream -> Word64
result str = AsEval.reify (cbpv str)
