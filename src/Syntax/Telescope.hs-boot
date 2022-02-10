module Syntax.Telescope where

import {-# SOURCE #-} Syntax.Semantic qualified as N
import {-# SOURCE #-} Normalization

data Telescope a

instance Eq a => Eq (Telescope a)

view :: Norm sig m => N.Term -> m (Telescope N.Term, N.Term)