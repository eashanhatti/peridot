module Elaboration.Term where

import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Surface
import Elaboration.Effect

check :: Elab sig m => TermAst -> N.Term -> m C.Term