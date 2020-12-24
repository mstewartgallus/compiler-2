{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cbpv.AsView (View, view) where

import Cbpv
import Control.Category
import Control.Monad.State
import Cbpv.Sort
import Prelude hiding ((.), id)

newtype View (a :: Sort t) (b :: Sort t) = V (State Int String)

view :: View a b -> String
view (V v) = evalState v 0

instance Category View where
  id = V $ pure "id"
  V f . V g = V $ pure (\f' g' -> "(" ++ f' ++ " ∘ " ++ g' ++ ")") <*> f <*> g

indent = unlines . map ("\t" ++) . lines

instance Code View where
  unit = V $ pure "unit"

  lift (V f) = V $ pure (\f' -> "(lift " ++ f' ++ ")") <*> f
  kappa _ f = V $ do
    v <- fresh
    let V body = f (V $ pure v)
    pure (\body' -> "(κ " ++ v ++ ". " ++ body' ++ ")") <*> body

instance Stack View where

instance Cbpv View View where
  thunk (V f) = V $ pure (\f' -> "thunk {" ++ indent ("\n" ++ f')  ++ "}") <*> f
  force (V f) = V $ pure (\f' -> "(force " ++ f' ++ ")") <*> f

  pass (V f) = V $ pure (\f' -> "(pass " ++ f' ++ ")") <*> f
  push (V f) = V $ pure (\f' -> "(push " ++ f' ++ ")") <*> f

  zeta t f = V $ do
    v <- fresh
    let V body = f (V $ pure v)
    body' <- body
    pure (\body' -> "(ζ " ++ v ++ ": " ++ "-" ++ ".\n" ++ body' ++ ")") <*> body
  pop t f = V $ do
    v <- fresh
    let V body = f (V $ pure v)
    body' <- body
    pure (\body' -> "(pop " ++ v ++ ".\n" ++ body' ++ ")") <*> body

  u64 x = V $ pure (show x)
  constant _ pkg name = V $ pure (pkg ++ "/" ++ name)
  cccIntrinsic x = V $ pure (show x)
  cbpvIntrinsic x = V $ pure (show x)

fresh :: State Int String
fresh = do
  n <- get
  put (n + 1)
  pure ("v" ++ show n)
