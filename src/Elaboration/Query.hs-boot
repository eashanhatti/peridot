module Elaboration.Query where

import Control.Effect.State(State)
import Control.Effect.Reader(Reader)
import Control.Algebra(Has)
import Syntax.Variable
import Syntax.Core qualified as C
import Normalization

data QueryState

data QueryContext

type Query sig m = (Has (Reader QueryContext) sig m, Has (State QueryState) sig m, Norm sig m)

data Key a where
  ElabDecl :: Id -> Key C.Declaration

query :: Query sig m => Key a -> m a