module Codegen.NormMeta where

import Syntax.Core qualified as C
import Syntax.Object qualified as O
import Control.Effect.NonDet
import Control.Algebra(Has)

type NormMeta sig m = Has NonDet sig m

normalize :: NormMeta sig m => C.Term -> m O.Term
normalize = undefined