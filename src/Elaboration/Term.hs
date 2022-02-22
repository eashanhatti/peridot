module Elaboration.Term where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Telescope qualified as T
import Syntax.Extra
import Elaboration.Effect
import Elaboration.Telescope qualified as ET
import Elaboration.Decl qualified as ED
import Control.Monad
import Normalization
import Data.List(foldl')

check :: Elab sig m => TermAst -> N.Term -> m C.Term
check term goal = case term of
  TermAst (Lam (map unName -> names) body) -> do
    (tele, outTy) <- T.view goal
    if T.size tele /= fromIntegral (length names) then do
      report TooManyParams
      pure C.EElabError
    else do
      cBody <- bindAll tele names (check body outTy)
      pure (C.FunIntro cBody)
  _ -> do
    (cTerm, ty) <- infer term
    unify goal ty
    pure cTerm

infer :: Elab sig m => TermAst -> m (C.Term, N.Term)
infer term = case term of
  TermAst (Pi (NameAst name) inTy outTy) -> do
    univ <- N.TypeType <$> freshStageUV
    cInTy <- check inTy univ
    vInTy <- eval cInTy
    cOutTy <- bindLocal name vInTy (check outTy univ)
    pure (C.FunType Explicit cInTy cOutTy, univ)
  TermAst (App lam args) -> do
    (cLam, lamTy) <- infer lam
    (cArgs, outTy) <- checkArgs args lamTy
    pure (foldl' (\lam arg -> C.FunElim lam arg) cLam cArgs, outTy)
    where
      checkArgs :: Elab sig m => [TermAst] -> N.Term -> m ([C.Term], N.Term)
      checkArgs [] outTy = pure ([], outTy)
      checkArgs (arg:args) (N.FunType _ inTy outTy) = do
        cArg <- check arg inTy
        vArg <- eval cArg
        (cArgs, outTy') <- appClosure outTy vArg >>= checkArgs args
        pure (cArg:cArgs, outTy')
  TermAst (Var name) -> do
    binding <- lookupBinding name
    case binding of
      Just (BLocal ix ty) -> pure (C.LocalVar ix, ty)
      Just (BGlobal did) -> do
        ty <- ED.declType did
        pure (C.GlobalVar did, ty)
  TermAst Univ -> do
    stage <- freshStageUV
    pure (C.TypeType stage, N.TypeType stage)
  TermAst (Let decls body) ->
    addDecls decls do
      cDecls <- traverse (ED.check . PDDecl) decls
      (cBody, bodyTy) <- infer body
      pure (C.Let cDecls cBody, bodyTy)
  TermAst (Rule phead pbody) -> do
    cTerm <- C.FunType Implicit <$> check pbody (N.TypeType Meta) <*> check phead (N.TypeType Meta)
    pure (cTerm, N.TypeType Meta)