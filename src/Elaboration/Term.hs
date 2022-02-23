module Elaboration.Term where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Extra
import Elaboration.Effect
import Elaboration.Decl qualified as ED
import Control.Monad
import Normalization
import Data.Foldable(foldl', foldr, foldrM)

check :: Elab sig m => TermAst -> N.Term -> m C.Term
check term goal = do
  (cTerm, ty) <- infer term
  unify goal ty
  pure cTerm

infer :: Elab sig m => TermAst -> m (C.Term, N.Term)
infer term = case term of
  TermAst (Lam (map unName -> names) body) -> do
    inTys <- traverse (const freshTypeUV) names
    cInTys <- traverse readbackWeak inTys
    outTy <- freshTypeUV
    cOutTy <- readbackWeak outTy
    let ty = foldr (\inTy outTy -> C.FunType Explicit inTy outTy) cOutTy (tail cInTys)
    vTy <- N.FunType Explicit (head inTys) <$> closureOf ty
    cBody <- checkBody (zip names inTys) outTy
    let lam = foldr (\_ body -> C.FunIntro body) cBody [0 .. length names - 1]
    pure (lam, vTy)
    where
      checkBody :: Elab sig m => [(Name, N.Term)] -> N.Term -> m C.Term
      checkBody [] outTy = check body outTy
      checkBody ((name, inTy):params) outTy = bindLocal name inTy (checkBody params outTy)
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
        ty <- ED.declType did >>= eval
        pure (C.GlobalVar did, ty)
  TermAst Univ -> do
    stage <- freshStageUV
    pure (C.TypeType stage, N.TypeType stage)
  TermAst (Let decls body) ->
    addDecls decls do
      cDecls <- traverse (ED.check . PDDecl) decls
      (cBody, bodyTy) <- infer body
      pure (C.Let cDecls cBody, bodyTy)
  TermAst (Rule outTy inTy) -> do
    cTerm <- C.FunType Implicit <$> check inTy (N.TypeType Meta) <*> check outTy (N.TypeType Meta)
    pure (cTerm, N.TypeType Meta)

checkType :: Elab sig m => TermAst -> m C.Term
checkType term = do
  stage <- freshStageUV
  check term (N.TypeType stage)

checkMetaType :: Elab sig m => TermAst -> m C.Term
checkMetaType term = check term (N.TypeType Meta)

checkObjectType :: Elab sig m => TermAst -> m C.Term
checkObjectType term = check term (N.TypeType Object)