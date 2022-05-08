module Normalization where

import Control.Algebra(Has)
import Control.Effect.Reader

data NormContext

type Norm sig m =
  ( Has (Reader NormContext) sig m )
