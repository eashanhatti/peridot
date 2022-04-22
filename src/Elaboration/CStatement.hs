module Elaboration.CStatement where

import Elaboration.Effect
import Syntax.Surface hiding(CStatement)
import Syntax.Core qualified as C
import Syntax.Common
import Syntax.Semantic qualified as N

infer :: Elab sig m => CStatementAst -> m (CStatement C.Term, N.Term)
infer = undefined
