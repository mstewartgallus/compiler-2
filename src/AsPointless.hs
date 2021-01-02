{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module AsPointless (asPointless) where

import qualified Cbpv as Cbpv
import qualified Cbpv.Hom as Cbpv
import Cbpv.Sort
import qualified Ccc.Type as Ccc
import Control.Monad.State hiding (lift)
import Data.Kind
import Data.Typeable ((:~:) (..))
import Dict
import qualified Lam.Type as Lam
import Pointless
import Pointless.Hom
import Prelude hiding (curry, drop, fst, id, snd, uncurry, (.))

asPointless :: Cbpv.Closed a b -> Hom @SetTag a b
asPointless x = case Cbpv.fold x of
  C y -> outC (evalState y 0)

newtype C (f :: Algebra -> Algebra -> Type) (g :: Set -> Set -> Type) a b = C (State Int (CS f g a b))

newtype K (f :: Algebra -> Algebra -> Type) (g :: Set -> Set -> Type) a b = K (State Int (KS f g a b))

instance Category g => Category (C f g) where
  id = C $ pure id
  C f . C g = C $ do
    f' <- f
    g' <- g
    pure (f' . g')

instance Category f => Category (K f g) where
  id = K $ pure id
  K f . K g = K $ do
    f' <- f
    g' <- g
    pure (f' . g')

instance Stack f => Cbpv.Stack (K f g)

instance Code g => Cbpv.Code (C f g) where
  unit = C $ pure unit
  kappa = kappa' inferSort
  lift (C f) (C x) = C $ do
    f' <- f
    x' <- x
    pure (f' . ((x' . unit) &&& id))

instance Pointless f g => Cbpv.Cbpv (K f g) (C f g) where
  thunk = thunk' inferSort
  force (C x) = K $ do
    x' <- x
    pure (push (force x') unit)

  push (K f) (C x) = K $ do
    f' <- f
    x' <- x
    pure (push f' x')
  pop = pop' inferSort

  pass (K f) (C x) = K $ do
    f' <- f
    x' <- x
    pure (pass f' x')
  zeta = zeta' inferSort

  u64 n = C $ pure (u64 n)
  cbpvIntrinsic x = C $ pure (cbpvIntrinsic x)

thunk' :: (Pointless f g, KnownSort a, KnownSort b) => SSet a -> (C f g Unit a -> K f g Empty b) -> C f g a (U b)
thunk' t f = C $ do
  v <- fresh t
  y <- case f (C $ pure $ var v) of
    K x -> x
  pure $
    thunk $ case removeVarK y v of
      Nothing -> y . drop
      Just x -> x

kappa' :: (Code g, KnownSort a, KnownSort b, KnownSort c) => SSet a -> (C f g Unit a -> C f g b c) -> C f g (a * b) c
kappa' t f = C $ do
  v <- fresh t
  y <- case f (C $ pure $ var v) of
    C x -> x
  pure $ case removeVarC y v of
    Nothing -> y . snd
    Just x -> x

pop' :: (Pointless f g, KnownSort a, KnownSort b, KnownSort c) => SSet a -> (C f g Unit a -> K f g b c) -> K f g (a & b) c
pop' t f = K $ do
  v <- fresh t
  y <- case f (C $ pure $ var v) of
    K x -> x
  pure $ case removeVarK y v of
    Nothing -> y . drop
    Just x -> x

zeta' :: (Pointless f g, KnownSort a, KnownSort b, KnownSort c) => SSet a -> (C f g Unit a -> K f g b c) -> K f g b (a ~> c)
zeta' t f = K $ do
  v <- fresh t
  y <- case f (C $ pure $ var v) of
    K x -> x
  pure $
    curry $ case removeVarK y v of
      Nothing -> y . drop
      Just x -> x

data CS (f :: Algebra -> Algebra -> Type) (g :: Set -> Set -> Type) b c = CS
  { outC :: g b c,
    removeVarC :: forall a. KnownSort a => Var a -> Maybe (CS f g (a * b) c)
  }

data KS (f :: Algebra -> Algebra -> Type) (g :: Set -> Set -> Type) b c = KS
  { outK :: f b c,
    removeVarK :: forall a. KnownSort a => Var a -> Maybe (KS f g (a & b) c)
  }

inC :: g a b -> CS f g a b
inC x =
  CS
    { outC = x,
      removeVarC = const Nothing
    }

inK :: f a b -> KS f g a b
inK x =
  KS
    { outK = x,
      removeVarK = const Nothing
    }

instance Category g => Category (CS f g) where
  id = inC id
  f . g =
    CS
      { outC = outC f . outC g,
        removeVarC = \v -> case (removeVarC f v, removeVarC g v) of
          (Just f', Just g') -> Just undefined
          (Nothing, Just g') -> Just (f . g')
          (Just f', Nothing) -> Just undefined
          (Nothing, Nothing) -> Nothing
      }

instance Category f => Category (KS f g) where
  id = inK id
  f . g =
    KS
      { outK = outK f . outK g,
        removeVarK = \v -> case (removeVarK f v, removeVarK g v) of
          (Just f', Just g') -> Just undefined
          (Nothing, Just g') -> Just (f . g')
          (Just f', Nothing) -> Just undefined
          (Nothing, Nothing) -> Nothing
      }

instance Stack f => Stack (KS f g)

instance Code g => Code (CS f g) where
  unit = inC unit
  fst = inC fst
  snd = inC snd
  x &&& y =
    CS
      { outC = outC x &&& outC y,
        removeVarC = \v -> case (removeVarC x v, removeVarC y v) of
          (Just x', Just y') -> Just (x' &&& y')
          (Nothing, Just y') -> Just ((x . snd) &&& y')
          (Just x', Nothing) -> Just (x' &&& (y . snd))
          (Nothing, Nothing) -> Nothing
      }

instance Pointless f g => Pointless (KS f g) (CS f g) where
  drop = inK drop
  push f x =
    KS
      { outK = push (outK f) (outC x),
        removeVarK = \v -> case (removeVarK f v, removeVarC x v) of
          (Just f', Just x') -> Just undefined
          (Nothing, Just x') -> Just undefined
          (Just f', Nothing) -> Just undefined
          (Nothing, Nothing) -> Nothing
      }

  force f =
    KS
      { outK = force (outC f),
        removeVarK = \v -> case removeVarC f v of
          Just f' -> Just undefined
          Nothing -> Nothing
      }
  thunk f =
    CS
      { outC = thunk (outK f),
        removeVarC = \v -> case removeVarK f v of
          Just f' -> Just undefined
          Nothing -> Nothing
      }

  uncurry f =
    KS
      { outK = uncurry (outK f),
        removeVarK = \v -> case removeVarK f v of
          Just f' -> Just undefined
          Nothing -> Nothing
      }
  curry f =
    KS
      { outK = curry (outK f),
        removeVarK = \v -> case removeVarK f v of
          Just f' -> Just undefined
          Nothing -> Nothing
      }
  u64 n = inC (u64 n)
  cbpvIntrinsic x = inC (cbpvIntrinsic x)

data Var a = Var (SSet a) Int

eqVar :: Var a -> Var b -> Maybe (a :~: b)
eqVar (Var at a) (Var bt b)
  | a == b = eqSort at bt
  | otherwise = Nothing

var :: (KnownSort a, Code g) => Var a -> CS f g Unit a
var v =
  CS
    { outC = error "free variable",
      removeVarC = \v' -> case eqVar v v' of
        Nothing -> Nothing
        Just Refl -> Just fst
    }

fresh :: SSet a -> State Int (Var a)
fresh t = do
  n <- get
  put (n + 1)
  pure (Var t n)
