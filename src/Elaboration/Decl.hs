module Elaboration.Decl where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Variable
import Elaboration.Effect

check :: Elab sig m => Id -> m C.Declaration
check = undefined