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

instance Pointless f g => Category (C f g) where
  id = C $ pure id
  C f . C g = C $ do
    f' <- f
    g' <- g
    pure (f' . g')

instance Pointless f g => Category (K f g) where
  id = K $ pure id
  K f . K g = K $ do
    f' <- f
    g' <- g
    pure (f' . g')

instance Pointless f g => Cbpv.Stack (K f g)

instance Pointless f g => Cbpv.Code (C f g) where
  unit = C $ pure unit
  fst = C $ pure fst
  snd = C $ pure snd
  C x &&& C y = C $ do
    x' <- x
    y' <- y
    pure (x' &&& y')

instance Pointless f g => Cbpv.Cbpv (K f g) (C f g) where
  thunk = thunk' inferSort
  force (C x) = K $ do
    x' <- x
    pure (force x' . inStack)

  push (C x) = K $ do
    x' <- x
    pure (lmapStack (x' . unit) . inStack)
  pop = pop' inferSort

  pass (C x) = K $ do
    x' <- x
    let p = lmapStack (x' . unit) . inStack
    pure (uncurry id . p)
  zeta = zeta' inferSort

  u64 n = C $ pure (u64 n)
  constant pkg name = C $ pure (constant pkg name)
  cbpvIntrinsic x = C $ pure (cbpvIntrinsic x)

thunk' :: (Pointless f g, KnownSort a, KnownSort b, KnownSort c) => SSet a -> (C f g Unit a -> K f g b c) -> C f g a (b ~. c)
thunk' t f = C $ do
  v <- fresh t
  y <- case f (C $ pure $ var v) of
    K x -> x
  pure $
    thunk $ case removeVarK y v of
      Nothing -> y . drop
      Just x -> x

kappa' :: (Pointless f g, KnownSort a, KnownSort b, KnownSort c) => SSet a -> (C f g Unit a -> C f g b c) -> C f g (a * b) c
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

instance Pointless f g => Category (CS f g) where
  id = inC id
  f . g =
    CS
      { outC = outC f . outC g,
        removeVarC = \v -> case (removeVarC f v, removeVarC g v) of
          (Just f', Just g') -> Just (f' . (fst &&& g'))
          (Nothing, Just g') -> Just (f . g')
          (Just f', Nothing) -> Just (f' . (fst &&& (g . snd)))
          (Nothing, Nothing) -> Nothing
      }

instance Pointless f g => Category (KS f g) where
  id = inK id
  f . g =
    KS
      { outK = outK f . outK g,
        removeVarK = \v -> case (removeVarK f v, removeVarK g v) of
          (Just f', Just g') -> Just (f' . rmapStack g' . push . lmapStack (id &&& id))
          (Nothing, Just g') -> Just (f . g')
          (Just f', Nothing) -> Just (f' . rmapStack g)
          (Nothing, Nothing) -> Nothing
      }

instance Pointless f g => Stack (KS f g)

instance Pointless f g => Code (CS f g) where
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
  inStack = inK inStack
  pop = inK pop
  push = inK push

  lmapStack x =
    KS
      { outK = lmapStack (outC x),
        removeVarK = \v -> case removeVarC x v of
          Just x' -> Just (lmapStack x' . pop)
          Nothing -> Nothing
      }

  rmapStack x =
    KS
      { outK = rmapStack (outK x),
        removeVarK = \v -> case removeVarK x v of
          Just x' -> Just (rmapStack x' . push . lmapStack (snd &&& fst) . pop)
          Nothing -> Nothing
      }

  force f =
    KS
      { outK = force (outC f),
        removeVarK = \v -> case removeVarC f v of
          Just f' -> Just (force f' . pop)
          Nothing -> Nothing
      }
  thunk f =
    CS
      { outC = thunk (outK f),
        removeVarC = \v -> case removeVarK f v of
          Just f' -> Just (thunk (f' . push))
          Nothing -> Nothing
      }

  uncurry f =
    KS
      { outK = uncurry (outK f),
        removeVarK = \v -> case removeVarK f v of
          Just f' -> Just (uncurry f' . push . lmapStack (snd &&& fst) . pop)
          Nothing -> Nothing
      }
  curry f =
    KS
      { outK = curry (outK f),
        removeVarK = \v -> case removeVarK f v of
          Just f' -> Just (curry (f' . push . lmapStack (snd &&& fst) . pop))
          Nothing -> Nothing
      }

  u64 n = inC (u64 n)
  constant pkg name = inC (constant pkg name)
  cbpvIntrinsic x = inC (cbpvIntrinsic x)

data Var a = Var (SSet a) Int

eqVar :: Var a -> Var b -> Maybe (a :~: b)
eqVar (Var at a) (Var bt b)
  | a == b = eqSort at bt
  | otherwise = Nothing

var :: (KnownSort a, Pointless f g) => Var a -> CS f g Unit a
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
