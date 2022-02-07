module Elaboration.Decl where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Variable
import {-# SOURCE #-} Elaboration.Query

check :: Query sig m => DeclarationAst -> m C.Declaration
check = undefined

checkQ :: Query sig m => Id -> m C.Declaration
checkQ did = query (ElabDecl did)