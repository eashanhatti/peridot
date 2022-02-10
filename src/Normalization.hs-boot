module Normalization where

import {-# SOURCE #-} Syntax.Core qualified as C
import {-# SOURCE #-} Syntax.Semantic qualified as N
import Control.Algebra(Has)
import Control.Effect.Reader

data NormContext

type Norm sig m = Has (Reader NormContext) sig m

evalClosure :: Norm sig m => N.Closure -> m N.Term