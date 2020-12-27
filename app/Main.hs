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

header :: AnsiStyle
header = underlined <> bold

main :: IO ()
main = do
  putDoc $
    annotate header (pretty "The Program:")
      <> hardline
      <> pretty program
      <> hardline
      <> hardline

  let compiled = AsCcc.asCcc program

  putDoc $
    annotate header (pretty "Kappa/Zeta Decomposition:")
      <> hardline
      <> pretty compiled
      <> hardline
      <> hardline

  let optimized = Ccc.optimize compiled

  putDoc $
    annotate header (pretty "Optimized Kappa/Zeta Decomposition:")
      <> hardline
      <> pretty optimized
      <> hardline
      <> hardline

  let cbpv = AsCallByName.toCbpv optimized

  putDoc $
    annotate header (pretty "Call By Push Value:")
      <> hardline
      <> pretty cbpv
      <> hardline
      <> hardline

  let optCbpv = Cbpv.opt cbpv

  putDoc $
    annotate header (pretty "Optimized Call By Push Value:")
      <> pretty optCbpv
      <> hardline
      <> hardline

  let result = Cbpv.reify optCbpv

  putDoc $
    annotate header (pretty "Result:")
      <> hardline
      <> pretty (show result)
      <> hardline
