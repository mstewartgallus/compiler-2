{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Pretty (Style (..), PrettyProgram (..), keyword, variable) where

import qualified Cbpv
import qualified Cbpv.Hom as Cbpv
import qualified Cbpv.Sort as Cbpv
import qualified Ccc
import qualified Ccc.Hom as Ccc
import qualified Ccc.Type as Ccc
import Control.Monad.State
import Data.Text.Prettyprint.Doc
import qualified Lam
import qualified Lam.Term as Lam
import qualified Lam.Type as Lam

data Style = None | Keyword | Variable

instance Semigroup Style

instance Monoid Style where
  mempty = None

keyword :: Doc Style -> Doc Style
keyword = annotate Keyword

variable :: Doc Style -> Doc Style
variable = annotate Variable

unitType :: Doc Style
unitType = keyword (pretty "1")

u64Type :: Doc Style
u64Type = keyword (pretty "u64")

fnType :: Doc Style -> Doc Style -> Doc Style
fnType a b = parens $ sep [a, keyword $ pretty "→", b]

tupleType :: Doc Style -> Doc Style -> Doc Style
tupleType a b = parens $ sep [a, keyword $ pretty "×", b]

ofType :: Doc Style
ofType = keyword (pretty ":")

bounds :: Doc Style
bounds = keyword (pretty "⇒")

bind :: Doc Style -> Doc Style -> Doc Style -> Doc Style -> Doc Style
bind q v t body =
  dent $
    vsep
      [ sep [q, v, ofType, t, bounds],
        body
      ]

class PrettyProgram p where
  prettyProgram :: p -> Doc Style

instance PrettyProgram (Lam.ST a) where
  prettyProgram expr = case expr of
    Lam.SUnit -> unitType
    Lam.SU64 -> u64Type
    a Lam.:-> b -> fnType (prettyProgram a) (prettyProgram b)

instance PrettyProgram (Lam.Term a) where
  prettyProgram x = evalState (viewLam (Lam.fold x) 0) 0

instance PrettyProgram (Ccc.ST a) where
  prettyProgram expr = case expr of
    Ccc.SUnit -> unitType
    Ccc.SU64 -> u64Type
    x Ccc.:*: y -> tupleType (prettyProgram x) (prettyProgram y)
    x Ccc.:-> y -> fnType (prettyProgram x) (prettyProgram y)

instance PrettyProgram (Ccc.Closed a b) where
  prettyProgram x = evalState (view (Ccc.fold x) 0) 0

instance PrettyProgram (Cbpv.SSort t a) where
  prettyProgram = go 0

-- shit!
instance PrettyProgram (Cbpv.Closed @Cbpv.SetTag a b) where
  prettyProgram x = evalState (view (Cbpv.fold x) 0) 0

go :: Int -> Cbpv.SSort t a -> Doc Style
go p x = case x of
  Cbpv.SUnit -> unitType
  Cbpv.SU64 -> u64Type
  Cbpv.SU x -> paren (p > appPrec) $ sep [keyword $ pretty "U", go (appPrec + 1) x]
  x Cbpv.:*: y -> paren (p > andPrec) $ sep [go (andPrec + 1) x, keyword $ pretty "×", go (andPrec + 1) y]
  Cbpv.SEmpty -> keyword $ pretty "i"
  x Cbpv.:&: y -> paren (p > asymPrec) $ sep [go (asymPrec + 1) x, keyword $ pretty "⊗", go (asymPrec + 1) y]
  x Cbpv.:-> y -> paren (p > expPrec) $ sep [go (expPrec + 1) x, keyword $ pretty "→", go (expPrec + 1) y]

appPrec :: Int
appPrec = 10

andPrec :: Int
andPrec = 4

asymPrec :: Int
asymPrec = 3

expPrec :: Int
expPrec = 9

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

dent :: Doc a -> Doc a
dent = nest 3

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
  pure $ paren (p > bePrec) $ bind (sep [x', keyword (pretty "be")]) v (prettyProgram t) body

lam' :: Lam.ST a -> (ViewLam a -> ViewLam b) -> ViewLam (a Lam.~> b)
lam' t f = VL $ \p -> do
  v <- fresh
  body <- viewLam (f (VL $ \_ -> pure v)) (lamPrec + 1)
  pure $ paren (p > lamPrec) $ bind (keyword (pretty "λ")) v (prettyProgram t) body

newtype View (a :: k) (b :: k) = V {view :: Int -> State Int (Doc Style)}

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
  pure $ paren (p > kappaPrec) $ bind (keyword $ pretty "κ") v (prettyProgram t) body

zeta' :: Ccc.ST a -> (View Ccc.Unit a -> View b c) -> View b (a Ccc.~> c)
zeta' t f = V $ \p -> do
  v <- fresh
  body <- view (f (V $ \_ -> pure v)) (zetaPrec + 1)
  pure $ paren (p > zetaPrec) $ bind (keyword $ pretty "ζ") v (prettyProgram t) body

instance Cbpv.Category (View @Cbpv.Set) where
  id = V $ \_ -> pure $ keyword $ pretty "id"
  f . g = V $ \p -> do
    f' <- view f (composePrec + 1)
    g' <- view g (composePrec + 1)
    pure $ paren (p > composePrec) $ sep [sep [f', keyword $ pretty "∘"], g']

instance Cbpv.Category (View @Cbpv.Algebra) where
  id = V $ \_ -> pure $ keyword $ pretty "skip"
  f . g = V $ \p -> do
    g' <- view g (composePrec + 1)
    f' <- view f (composePrec + 1)
    pure $ paren (p > composePrec) $ vsep [sep [g', keyword $ pretty ";"], f']

instance Cbpv.Code View where
  unit = V $ \_ -> pure $ keyword $ pretty "!"

  lift x = V $ \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "lift", x']) <*> view x (appPrec + 1)
  kappa = kappaCbpv Cbpv.inferSort

instance Cbpv.Stack View

instance Cbpv.Cbpv View View where
  force x = V $ \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "force", x']) <*> view x (appPrec + 1)
  thunk = thunk' Cbpv.inferSort

  push x = V $ \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "push", x']) <*> view x (appPrec + 1)
  pop = pop' Cbpv.inferSort

  pass x = V $ \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "pass", x']) <*> view x (appPrec + 1)
  zeta = zetaCbpv Cbpv.inferSort

  u64 n = V $ \_ -> pure (pretty n)
  constant pkg name = V $ \p -> pure $ paren (p > appPrec) $ sep [keyword $ pretty "call", pretty (pkg ++ "/" ++ name)]
  cccIntrinsic x = V $ \p -> pure $ paren (p > appPrec) $ sep [keyword $ pretty "ccc", pretty $ show x]
  cbpvIntrinsic x = V $ \p -> pure $ paren (p > appPrec) $ sep [keyword $ pretty "cbpv", pretty $ show x]

thunk' :: Cbpv.SSet a -> (View Cbpv.Unit a -> View Cbpv.Empty c) -> View a (Cbpv.U c)
thunk' t f =
  V $ \p -> do
    v <- fresh
    body <- view (f (V $ \_ -> pure v)) (zetaPrec + 1)
    pure $ paren (p > zetaPrec) $ bind (keyword $ pretty "thunk") v (prettyProgram t) body

kappaCbpv :: Cbpv.SSet a -> (View Cbpv.Unit a -> View b c) -> View (a Cbpv.* b) c
kappaCbpv t f =
  V $ \p -> do
    v <- fresh
    body <- view (f (V $ \_ -> pure v)) (kappaPrec + 1)
    pure $ paren (p > zetaPrec) $ bind (keyword $ pretty "κ") v (prettyProgram t) body

pop' :: Cbpv.SSet a -> (View Cbpv.Unit a -> View b c) -> View (a Cbpv.& b) c
pop' t f =
  V $ \p -> do
    v <- fresh
    body <- view (f (V $ \_ -> pure v)) (kappaPrec + 1)
    pure $ paren (p > kappaPrec) $ bind (keyword $ pretty "pop") v (prettyProgram t) body

zetaCbpv :: Cbpv.SSet a -> (View Cbpv.Unit a -> View b c) -> View b (a Cbpv.~> c)
zetaCbpv t f = V $ \p -> do
  v <- fresh
  body <- view (f (V $ \_ -> pure v)) (zetaPrec + 1)
  pure $ paren (p > zetaPrec) $ bind (keyword $ pretty "ζ") v (prettyProgram t) body
