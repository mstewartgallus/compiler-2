module Pretty (Style (..), PrettyProgram (..), keyword, variable) where

import Data.Text.Prettyprint.Doc

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
