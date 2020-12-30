{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}

module Dict (Dict (..)) where

data Dict c = c => Dict
