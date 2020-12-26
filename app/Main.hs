module Main where

import qualified AsCallByName
import qualified AsCcc
import qualified Cbpv.AsEval as Cbpv
import qualified Cbpv.AsOpt as Cbpv
import qualified Cbpv.Hom as Cbpv
import qualified Ccc.Hom as Ccc
import qualified Ccc.Optimize as Ccc
import qualified Ccc.Type
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

  let optimized = Ccc.optimize compiled

  putStrLn ""
  putStrLn "Optimized Program"
  putStrLn (show optimized)

  let cbpv = AsCallByName.toCbpv optimized

  putStrLn ""
  putStrLn "Cbpv Program"
  putStrLn (show cbpv)

  let optCbpv = Cbpv.opt cbpv

  putStrLn ""
  putStrLn "Cbpv Optimized"
  putStrLn (show optCbpv)

  let result = Cbpv.reify optCbpv

  putStrLn ""
  putStrLn "Result"
  putStrLn (show result)
