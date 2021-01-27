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
paren x = iff x parens

iff :: Bool -> (a -> a) -> (a -> a)
iff True f y = f y
iff _ _ y = y

fresh :: State Int (Doc Style)
fresh = do
  n <- get
  put (n + 1)
  pure $ variable (pretty "v" <> pretty n)

class PrettyProgram p where
  prettyProgram :: p -> Doc Style

instance PrettyProgram (Lam.Term a) where
  prettyProgram x = evalState (viewLam (Lam.fold x) 0) 0

instance PrettyProgram (Ccc.Closed a b) where
  prettyProgram x = evalState (view (Ccc.fold x) 0) 0

instance PrettyProgram (Cbpv.SSet a) where
  prettyProgram = go 0

instance PrettyProgram (Cbpv.SAlgebra a) where
  prettyProgram = goAlg 0

-- shit!
instance PrettyProgram (Cbpv.Closed @Cbpv.Set a b) where
  prettyProgram x = evalState (view (Cbpv.fold x) 0) 0

go :: Int -> Cbpv.SSet a -> Doc Style
go p x = case x of
  Cbpv.SUnit -> unitType
  Cbpv.SU64 -> u64Type
  x Cbpv.:-. y -> paren (p > appPrec) $ sep [goAlg (expPrec + 1) x, keyword $ pretty "⊸", goAlg (expPrec + 1) y]
  x Cbpv.:*: y -> paren (p > andPrec) $ sep [go (andPrec + 1) x, keyword $ pretty "×", go (andPrec + 1) y]

goAlg :: Int -> Cbpv.SAlgebra a -> Doc Style
goAlg p x = case x of
  Cbpv.SEmpty -> keyword $ pretty "i"
  x Cbpv.:&: y -> paren (p > asymPrec) $ sep [go (asymPrec + 1) x, keyword $ pretty "⊗", goAlg (asymPrec + 1) y]
  x Cbpv.:-> y -> paren (p > expPrec) $ sep [go (expPrec + 1) x, keyword $ pretty "→", goAlg (expPrec + 1) y]

-- shit!

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

newtype ViewLamT (a :: Lam.T) = VLT (Doc Style)

instance Lam.Tagged ViewLamT where
  unitTag = VLT unitType
  u64Tag = VLT u64Type
  expTag (VLT a) (VLT b) = VLT (fnType a b)

be' :: ViewLamT a -> ViewLam a -> (ViewLam a -> ViewLam b) -> ViewLam b
be' (VLT t) x f = VL $ \p -> do
  x' <- viewLam x (bePrec + 1)
  v <- fresh
  body <- viewLam (f (VL $ \_ -> pure v)) (bePrec + 1)
  pure $ paren (p > bePrec) $ bind (sep [x', keyword (pretty "be")]) v t body

lam' :: ViewLamT a -> (ViewLam a -> ViewLam b) -> ViewLam (a Lam.~> b)
lam' (VLT t) f = VL $ \p -> do
  v <- fresh
  body <- viewLam (f (VL $ \_ -> pure v)) (lamPrec + 1)
  pure $ paren (p > lamPrec) $ bind (keyword (pretty "λ")) v t body

newtype ViewLamC (a :: Ccc.T) = VLC (Doc Style)

instance Ccc.Tagged ViewLamC where
  unitTag = VLC unitType
  u64Tag = VLC u64Type
  tupleTag (VLC x) (VLC y) = VLC (tupleType x y)
  expTag (VLC x) (VLC y) = VLC (fnType x y)

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

kappa' :: ViewLamC a -> (View Ccc.Unit a -> View b c) -> View (a Ccc.* b) c
kappa' (VLC t) f = V $ \p -> do
  v <- fresh
  body <- view (f (V $ \_ -> pure v)) (kappaPrec + 1)
  pure $ paren (p > kappaPrec) $ bind (keyword $ pretty "κ") v t body

zeta' :: ViewLamC a -> (View Ccc.Unit a -> View b c) -> View b (a Ccc.~> c)
zeta' (VLC t) f = V $ \p -> do
  v <- fresh
  body <- view (f (V $ \_ -> pure v)) (zetaPrec + 1)
  pure $ paren (p > zetaPrec) $ bind (keyword $ pretty "ζ") v t body

instance Cbpv.Code View where
  id = V $ \_ -> pure $ keyword $ pretty "id"
  f . g = V $ \p -> do
    f' <- view f (composePrec + 1)
    g' <- view g (composePrec + 1)
    pure $ paren (p > composePrec) $ sep [sep [f', keyword $ pretty "∘"], g']

  unit = V $ \_ -> pure $ keyword $ pretty "!"
  fst = V $ \_ -> pure $ keyword $ pretty "π₁"
  snd = V $ \_ -> pure $ keyword $ pretty "π₁"
  f &&& g = V $ \p -> do
    f' <- view f (composePrec + 1)
    g' <- view g (composePrec + 1)
    pure $ iff (p > composePrec) angles $ sep [f', keyword $ pretty ",", g']

instance Cbpv.Stack View where
  skip = V $ \_ -> pure $ keyword $ pretty "skip"
  f <<< g = V $ \p -> do
    g' <- view g (composePrec + 1)
    f' <- view f (composePrec + 1)
    pure $ paren (p > composePrec) $ vsep [sep [g', keyword $ pretty ";"], f']

instance Cbpv.Cbpv View View where
  force x = V $ \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "force", x']) <*> view x (appPrec + 1)
  thunk = thunk' Cbpv.inferSet

  push x = V $ \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "push", x']) <*> view x (appPrec + 1)
  pop = pop' Cbpv.inferSet

  pass x = V $ \p -> pure (\x' -> paren (p > appPrec) $ sep [keyword $ pretty "pass", x']) <*> view x (appPrec + 1)
  zeta = zetaCbpv Cbpv.inferSet

  u64 n = V $ \_ -> pure (pretty n)
  constant pkg name = V $ \p -> pure $ paren (p > appPrec) $ sep [keyword $ pretty "call", pretty (pkg ++ "/" ++ name)]
  cccIntrinsic x = V $ \p -> pure $ paren (p > appPrec) $ sep [keyword $ pretty "ccc", pretty $ show x]
  cbpvIntrinsic x = V $ \p -> pure $ paren (p > appPrec) $ sep [keyword $ pretty "cbpv", pretty $ show x]

thunk' :: Cbpv.SSet a -> (View Cbpv.Unit a -> View b c) -> View a (b Cbpv.~. c)
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

newtype ViewP (a :: t) (b :: t) = VP {viewP :: Int -> Doc Style}
