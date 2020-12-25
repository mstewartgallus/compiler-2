module Ccc.AsRepeat (repeat) where

import Ccc
import qualified Ccc.AsSimplified as AsSimplified
import Control.Category
import Ccc.Type
import Ccc.Hom
import Prelude hiding ((.), id, repeat)

repeat :: Int -> Closed a b -> Closed a b
repeat = loop

loop :: Int -> Closed a b -> Closed a b
loop n x | n == 0 = x
         | otherwise = loop (n - 1) (AsSimplified.simplify x)
