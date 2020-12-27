module Main where

import qualified AsCallByName
import qualified AsCcc
import qualified Cbpv.AsEval as Cbpv
import qualified Cbpv.AsOpt as Cbpv
import qualified Cbpv.Hom as Cbpv
import qualified Ccc.Hom as Ccc
import qualified Ccc.Optimize as Ccc
import qualified Ccc.Type
import Data.Text.Prettyprint.Doc
import Lam
import qualified Lam.Term as Lam
import Lam.Type
import Prettyprinter.Render.Terminal
import Prelude hiding ((<*>))

program :: Lam.Closed U64
program =
  Lam.Closed $
    u64 3 `letBe` \z ->
      add <*> z <*> z

main :: IO ()
main = do
  putStrLn "The Program"
  putDoc (pretty program)
  putStrLn ""
  putStrLn ""

  let compiled = AsCcc.asCcc program

  putStrLn "Kappa/Zeta Decomposition"
  putDoc (pretty compiled)
  putStrLn ""
  putStrLn ""

  let optimized = Ccc.optimize compiled

  putStrLn "Optimized Program"
  putDoc (pretty optimized)
  putStrLn ""

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
