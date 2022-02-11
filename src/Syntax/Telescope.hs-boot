module Syntax.Telescope where

import {-# SOURCE #-} Syntax.Semantic qualified as N
import {-# SOURCE #-} Normalization
import Numeric.Natural

data Telescope a

instance Eq a => Eq (Telescope a)

instance Foldable Telescope

view :: Norm sig m => N.Term -> m (Telescope N.Term, N.Term)

size :: Telescope a -> Natural