{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.AsScheme (toScheme) where

import Cbpv
import qualified Cbpv.Hom as Hom
import Data.Word
import Cbpv.Sort
import qualified Ccc.Type as Ccc
import qualified Ccc as Ccc
import qualified Lam.Type as Lam
import Prelude hiding ((.), id)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable ((:~:) (..))
import Data.Text.Prettyprint.Doc
import Pretty
import Control.Monad.State hiding (lift)

toScheme :: Hom.Closed (U (F Unit)) (U (F U64)) -> Doc Style
toScheme x = case Hom.fold x of
  P y -> evalState y 0

-- go :: Prog (U (F Unit)) (U (F U64)) -> Word64
-- go (C f) = case f (Thunk $ \w -> Unit :& w) of
--   Thunk t -> case t (Effect 0) of
--     (U64 y :& _) -> y

newtype Prog (a :: Sort t) (b :: Sort t) = P { comp :: State Int (Doc Style) }

instance Category (Prog @SetTag) where
  id = P $ do
    v <- fresh
    pure $ parens $ sep [sep [pretty "lambda", parens v], v]
  P f . P g = P $ do
    g' <- g
    f' <- f
    v <- fresh
    pure $ parens $ sep [sep [pretty "lambda", parens v], parens (sep [f', parens (sep [g', v])])]
instance Category (Prog @AlgebraTag) where
  id = P $ pure (pretty "")
  P f . P g = P $ do
    g' <- g
    f' <- f
    pure (vsep [g', f'])

instance Code Prog where
  unit = P $ pure (pretty "'()")
  fst = P $ pure $ pretty "fst"
  snd = P $ pure $ pretty "snd"
  P x &&& P y = P $ do
    x' <- x
    y' <- y
    pure $ parens $ sep [x', pretty ".", y']

instance Stack Prog where

instance Cbpv Prog Prog where
  force (P x) = P $ do
    x' <- x
    pure $ parens $ sep [pretty "force", x']
  thunk f = P $ do
    v <- fresh
    body <- comp (f (P $ pure v))
    pure $ parens $ dent $ vsep [sep [pretty "thunk", parens v], body]

  pass (P x) = P $ do
    x' <- x
    pure $ parens $ sep [pretty "pass", x']
  zeta f = P $ do
    v <- fresh
    body <- comp (f (P $ pure v))
    pure $ parens $ dent $ vsep [sep [pretty "zeta", parens v], body]

  lift (P x) = P $ do
    x' <- x
    pure $ parens $ sep [pretty "push", x']
  pop f = P $ do
    v <- fresh
    body <- comp (f (P $ pure v))
    pure $ parens $ dent $ vsep [sep [pretty "pop", parens v], body]

  u64 n = P $ pure $ pretty n
  constant pkg name = P $ do
    pure $ parens $ sep [pretty "call", pretty pkg, pretty name]
  cbpvIntrinsic x = P $ case x of
     AddIntrinsic -> pure $ pretty "add-intrinsic"

fresh :: State Int (Doc Style)
fresh = do
  n <- get
  put (1 + n)
  pure (pretty "v" <> pretty n)

dent :: Doc a -> Doc a
dent = nest 3
