{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
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
  C y -> evalState (y $ pretty "'()") 0

-- go :: Prog (U (F Unit)) (U (F U64)) -> Word64
-- go (C f) = case f (Thunk $ \w -> Unit :& w) of
--   Thunk t -> case t (Effect 0) of
--     (U64 y :& _) -> y

data family Prog (a :: Sort t) (b :: Sort t)
newtype instance Prog (a :: Set) (b :: Set) = C (Doc Style -> State Int (Doc Style))
newtype instance Prog (a :: Algebra) (b :: Algebra) = K { comp :: State Int (Doc Style) }

instance Category (Prog @SetTag) where
  -- id = P $ do
  --   v <- fresh
  --   pure $ parens $ sep [sep [pretty "lambda", parens v], v]
  C f . C g = C $ \x -> do
    y <- g x
    f y
instance Category (Prog @AlgebraTag) where
  -- id = K $ pure (pretty "")
  K f . K g = K $ do
    g' <- g
    f' <- f
    pure $ parens $ vsep [f', g']

instance Code Prog where
  unit = C $ \_ -> pure (pretty "'()")
  -- fst = P $ pure $ pretty "fst"
  -- snd = P $ pure $ pretty "snd"
  C x &&& C y = C $ \env -> do
    x' <- x env
    y' <- y env
    pure $ sep [x', y']

instance Stack Prog where

instance Cbpv Prog Prog where
  force (C x) = K $ do
    x' <- x $ pretty "'()"
    pure $ parens $ sep [pretty "force", x']
  thunk f = C $ \env -> do
    body <- comp (f (C $ \_ -> pure env))
    pure $ parens $ dent $ vsep [pretty "delay", body]

  pass (C x) = K $ do
    x' <- x $ pretty "'()"
    pure $ sep [pretty "pass", x']
  zeta f = K $ do
    v <- fresh
    body <- comp (f (C $ \_ -> pure v))
    pure $ parens $ dent $ vsep [sep [pretty "lambda", parens v], body]

  lift (C x) = K $ do
    x' <- x $ pretty "'()"
    pure x' -- $ parens $ sep [pretty "push", x']

  pop f = K $ do
    v <- fresh
    body <- comp (f (C $ \_ -> pure v))
    pure $ parens $ dent $ vsep [sep [pretty "lambda", parens v], body]

  u64 n = C $ \_ -> pure $ pretty n
  constant pkg name = K $ do
    pure $ parens $ sep [pretty "call", pretty pkg, pretty name]
  cbpvIntrinsic x = C $ \args -> case x of
     AddIntrinsic -> pure $ parens $ sep [pretty "+", args]

fresh :: State Int (Doc Style)
fresh = do
  n <- get
  put (1 + n)
  pure (pretty "v" <> pretty n)

dent :: Doc a -> Doc a
dent = nest 3
