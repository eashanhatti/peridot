module Elaboration.Term where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Telescope qualified as T
import Elaboration.Query
import Elaboration.Telescope qualified as ET
import Control.Monad

check :: TermAst -> N.Term -> Query C.Term
check (TermAst (Lam (map unName -> bindings) body)) goal = do
  let (tele, outTy) = ET.view goal
  bindAll tele bindings (check body outTy)