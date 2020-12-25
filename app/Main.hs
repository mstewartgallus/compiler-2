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

program :: Lam.Closed U64
program =
  Lam.Closed $
    u64 3 `letBe` \z ->
      add <*> z <*> z

main :: IO ()
main = do
  putStrLn "The Program"
  putStrLn (show program)

  let compiled = AsCcc.asCcc program

  putStrLn ""
  putStrLn "Kappa/Zeta Decomposition"
  putStrLn (show compiled)

  let optimized = opt compiled

  putStrLn ""
  putStrLn "Optimized Program"
  putStrLn (show optimized)

  let cbpv = toCbpv optimized

  putStrLn ""
  putStrLn "Cbpv Program"
  putStrLn (show cbpv)

  let optCbpv = AsOpt.opt cbpv

  putStrLn ""
  putStrLn "Cbpv Optimized"
  putStrLn (show optCbpv)

  let result = AsEval.reify optCbpv

  putStrLn ""
  putStrLn "Result"
  putStrLn (show result)
