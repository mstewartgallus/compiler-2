{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Pretty (Style (..), PrettyProgram (..), keyword, variable) where

import qualified Ccc
import qualified Ccc.Hom as Ccc
import qualified Ccc.Type as Ccc
import Control.Monad.State
import Data.Text.Prettyprint.Doc
import qualified Lam
import qualified Lam.Term as Lam
import qualified Lam.Type as Lam

data Style = None | Keyword | Variable

keyword :: Doc Style -> Doc Style
keyword = annotate Keyword

variable :: Doc Style -> Doc Style
variable = annotate Variable

instance Semigroup Style

instance Monoid Style where
  mempty = None

class PrettyProgram p where
  prettyProgram :: p -> Doc Style

instance PrettyProgram (Lam.ST a) where
  prettyProgram expr = case expr of
    Lam.SUnit -> keyword $ pretty "1"
    Lam.SU64 -> keyword $ pretty "u64"
    x Lam.:-> y -> parens $ sep [prettyProgram x, keyword $ pretty "→", prettyProgram y]

instance PrettyProgram (Lam.Term a) where
  prettyProgram x = evalState (viewLam (Lam.fold x) 0) 0

instance Pretty (Ccc.ST a) where
  pretty expr = case expr of
    Ccc.SUnit -> pretty "1"
    Ccc.SU64 -> pretty "u64"
    x Ccc.:*: y -> parens $ sep [pretty x, pretty "×", pretty y]
    x Ccc.:-> y -> parens $ sep [pretty x, pretty "→", pretty y]

instance PrettyProgram (Ccc.Closed a b) where
  prettyProgram x = evalState (view (Ccc.fold x) 0) 0

appPrec :: Int
appPrec = 10

kappaPrec :: Int
kappaPrec = 2

zetaPrec :: Int
zetaPrec = 5

composePrec :: Int
composePrec = 9

lamPrec :: Int
lamPrec = 9

bePrec :: Int
bePrec = 8

paren :: Bool -> Doc Style -> Doc Style
paren x = if x then parens else id

fresh :: State Int (Doc Style)
fresh = do
  n <- get
  put (n + 1)
  pure $ variable (pretty "v" <> pretty n)

newtype ViewLam (a :: Lam.T) = VL {viewLam :: Int -> State Int (Doc Style)}

instance Lam.Lam ViewLam where
  be = be' Lam.inferT
  lam = lam' Lam.inferT

  f <*> x = VL $ \p -> do
    f' <- viewLam f (appPrec + 1)
    x' <- viewLam x (appPrec + 1)
    pure $ paren (p > appPrec) $ sep [f', x']

  u64 n = VL $ \_ -> pure (pretty n)
  constant pkg name = VL $ \_ -> pure $ pretty (pkg ++ "/" ++ name)

be' :: Lam.ST a -> ViewLam a -> (ViewLam a -> ViewLam b) -> ViewLam b
be' t x f = VL $ \p -> do
  x' <- viewLam x (bePrec + 1)
  v <- fresh
  body <- viewLam (f (VL $ \_ -> pure v)) (bePrec + 1)
  let binder = sep [v, keyword (pretty ":"), prettyProgram t]
  pure $ paren (p > bePrec) $ vsep [sep [x', keyword (pretty "be"), binder, keyword (pretty "⇒")], body]

lam' :: Lam.ST a -> (ViewLam a -> ViewLam b) -> ViewLam (a Lam.~> b)
lam' t f = VL $ \p -> do
  v <- fresh
  body <- viewLam (f (VL $ \_ -> pure v)) (lamPrec + 1)
  pure $ paren (p > lamPrec) $ sep [keyword (pretty "λ"), v, keyword (pretty ":"), prettyProgram t, keyword (pretty "⇒"), body]

newtype View (a :: Ccc.T) (b :: Ccc.T) = V {view :: Int -> State Int (Doc Style)}

instance Ccc.Ccc View where
  id = V $ \_ -> pure $ keyword (pretty "id")
  f . g = V $ \p -> do
    f' <- view f (composePrec + 1)
    g' <- view g (composePrec + 1)
    pure $ paren (p > composePrec) $ sep [f', keyword $ pretty "∘", g']

  unit = V $ \_ -> pure $ keyword $ pretty "!"

  lift x = V $ \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "lift", x']) <*> view x (appPrec + 1)
  kappa = kappa' Ccc.inferT

  pass x = V $ \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "pass", x']) <*> view x (appPrec + 1)
  zeta = zeta' Ccc.inferT

  u64 n = V $ \_ -> pure (pretty n)
  constant pkg name = V $ \_ -> pure $ pretty (pkg ++ "/" ++ name)
  cccIntrinsic x = V $ \_ -> pure $ pretty (show x)

kappa' :: Ccc.ST a -> (View Ccc.Unit a -> View b c) -> View (a Ccc.* b) c
kappa' t f = V $ \p -> do
  v <- fresh
  body <- view (f (V $ \_ -> pure v)) (kappaPrec + 1)
  pure $ paren (p > kappaPrec) $ sep [keyword $ pretty "κ", v, keyword $ pretty ":", pretty t, keyword $ pretty "⇒", body]

zeta' :: Ccc.ST a -> (View Ccc.Unit a -> View b c) -> View b (a Ccc.~> c)
zeta' t f = V $ \p -> do
  v <- fresh
  body <- view (f (V $ \_ -> pure v)) (zetaPrec + 1)
  pure $ paren (p > zetaPrec) $ sep [keyword $ pretty "ζ", v, keyword $ pretty ":", pretty t, keyword $ pretty "⇒", body]
