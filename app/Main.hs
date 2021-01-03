module Main where

import qualified AsC
import qualified AsCallByName
import qualified AsCcc
import qualified AsPointless
import qualified AsScheme
import qualified Cbpv.AsOpt as Cbpv
import qualified Cbpv.Hom as Cbpv
import qualified Ccc.Hom as Ccc
import qualified Ccc.Optimize as Ccc
import qualified Ccc.Type
import Data.Text.Prettyprint.Doc
import qualified Interpreter
import Lam
import qualified Lam.Term as Lam
import Lam.Type
import qualified Pointless
import Pretty
import Prettyprinter.Render.Terminal
import Prelude hiding ((<*>))

program :: Lam.Term U64
program =
  Lam.mkTerm $
    u64 3 `be` \z ->
      (z - z) + (z + z)

header :: AnsiStyle
header = underlined <> bold

toAnsi :: Style -> AnsiStyle
toAnsi s = case s of
  None -> mempty
  Keyword -> bold
  Variable -> italicized

main :: IO ()
main = do
  putDoc $
    annotate header (pretty "The Program:")
      <> hardline
      <> reAnnotate toAnsi (prettyProgram program)
      <> hardline
      <> hardline

  let compiled = AsCcc.asCcc program

  putDoc $
    annotate header (pretty "Kappa/Zeta Decomposition:")
      <> hardline
      <> reAnnotate toAnsi (prettyProgram compiled)
      <> hardline
      <> hardline

  let optimized = Ccc.optimize compiled

  putDoc $
    annotate header (pretty "Optimized Kappa/Zeta Decomposition:")
      <> hardline
      <> reAnnotate toAnsi (prettyProgram optimized)
      <> hardline
      <> hardline

  let cbpv = AsCallByName.toCbpv optimized

  putDoc $
    annotate header (pretty "Call By Push Value:")
      <> hardline
      <> reAnnotate toAnsi (prettyProgram cbpv)
      <> hardline
      <> hardline

  let optCbpv = Cbpv.opt cbpv

  putDoc $
    annotate header (pretty "Optimized Call By Push Value:")
      <> hardline
      <> reAnnotate toAnsi (prettyProgram optCbpv)
      <> hardline
      <> hardline

  let result = case Interpreter.interpret optCbpv (Interpreter.Thunk (Interpreter.Unit Interpreter.:&)) of
        Interpreter.Thunk y -> case y (Interpreter.Effect 0) of
          Interpreter.U64 x Interpreter.:& _ -> x

  putDoc $
    annotate header (pretty "Result:")
      <> hardline
      <> pretty (show result)
      <> hardline
      <> hardline

  let pointless = AsPointless.asPointless optCbpv

  putDoc $
    annotate header (pretty "Pointless Prototype:")
      <> hardline
      <> reAnnotate toAnsi (prettyProgram pointless)
      <> hardline
      <> hardline

  let scheme = AsScheme.toScheme pointless

  putDoc $
    annotate header (pretty "Scheme Prototype:")
      <> hardline
      <> reAnnotate toAnsi scheme
      <> hardline
      <> hardline

  let cprog = AsC.toC pointless

  putDoc $
    annotate header (pretty "C Prototype:")
      <> hardline
      <> reAnnotate toAnsi cprog
      <> hardline
      <> hardline
