module Elaboration.Term where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Telescope qualified as T
import Syntax.Stage
import Elaboration.Query
import Elaboration.Telescope qualified as ET
import Elaboration.Decl qualified as ED
import Control.Monad

check :: Query sig m => TermAst -> N.Term -> m C.Term
check (TermAst (Pi tele outTy)) goal = undefined  
check (TermAst (Lam (map unName -> bindings) body)) goal = do
  (tele, outTy) <- ET.view goal
  bindAll tele bindings (check body outTy)
check (TermAst Univ) (N.TypeType stage) = pure (C.TypeType stage)
check (TermAst (Let decls body)) goal = do
  addDecls decls do
    cDecls <- traverse ED.checkQ (map unId decls)
    cBody <- check body goal
    pure (C.Let cDecls cBody)