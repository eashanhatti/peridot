module Elaboration.Term where

import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Surface
import Elaboration.Effect

infer :: Elab sig m => TermAst -> m (C.Term, N.Term)

check :: Elab sig m => TermAst -> N.Term -> m C.Term

-- checkType :: Elab sig m => TermAst -> m (C.Term, N.Term)

checkMetaType :: Elab sig m => TermAst -> m (C.Term, N.Term)

checkObjType :: Elab sig m => TermAst -> m (C.Term, N.Term)

checkLowCType :: Elab sig m => TermAst -> m (C.Term, N.Term)

checkLowCType' :: Elab sig m => TermAst -> m C.Term
