module Elaboration.Term where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Telescope qualified as T
import Syntax.Stage
import Elaboration.Effect
import Elaboration.Telescope qualified as ET
import Elaboration.Decl qualified as ED
import Control.Monad

check :: Elab sig m => TermAst -> N.Term -> m C.Term
check (TermAst (Lam (map unName -> bindings) body)) goal = do
  (tele, outTy) <- T.view goal
  bindAll tele bindings (check body outTy)
check (TermAst (Let decls body)) goal = do
  addDecls decls do
    cDecls <- traverse ED.check (map unId decls)
    cBody <- check body goal
    pure (C.Let cDecls cBody)
check term goal = do
  ty <- infer term
  unify goal ty

infer :: Elab sig m => TermAst -> m N.Term
infer (Pi (unName -> name) inTy outTy) = do
  univ <- N.TypeType <$> freshStageUV
  cInTy <- check inTy univ
  vInTy <- eval cInTy
  cOutTy <- bindLocal name vInTy (check outTy univ)
  pu