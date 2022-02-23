module Elaboration.Term where

import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Surface
import Elaboration.Effect

check :: Elab sig m => TermAst -> N.Term -> m C.Term

checkType :: Elab sig m => TermAst -> m C.Term

checkMetaType :: Elab sig m => TermAst -> m C.Term

checkObjectType :: Elab sig m => TermAst -> m C.Term