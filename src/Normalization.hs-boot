module Normalization where

import {-# SOURCE #-} Syntax.Core qualified as C
import {-# SOURCE #-} Syntax.Semantic qualified as N
import Control.Algebra(Has)
import Control.Effect.Reader
import Control.Effect.State

data NormContext

data NormState

type Norm sig m =
  ( Has (Reader NormContext) sig m
  , Has (State NormState) sig m )

evalClosure :: Norm sig m => N.Closure -> m N.Term