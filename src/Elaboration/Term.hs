module Elaboration.Term where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Extra hiding(unId)
import Elaboration.Effect
import Elaboration.Decl qualified as ED
import Control.Monad
import Normalization hiding(eval)
import Data.Foldable(foldl', foldr, foldrM)
import Debug.Trace

check :: Elab sig m => TermAst -> N.Term -> m C.Term
check term goal = do
  (cTerm, ty) <- infer term
  unify goal ty
  pure cTerm

infer :: Elab sig m => TermAst -> m (C.Term, N.Term)
infer term = case term of
  SourcePos term pos -> withPos pos (infer term)
  TermAst (Lam (map unName -> names) body) -> do
    inTys <- traverse (const freshTypeUV) names
    cInTys <- traverse readbackWeak inTys
    outTy <- freshTypeUV
    cOutTy <- readbackWeak outTy
    let ty = foldr (\inTy outTy -> C.FunType Explicit inTy outTy) cOutTy (tail cInTys)
    vTy <- N.FunType Explicit (head inTys) <$> closureOf ty
    cBody <- checkBody (zip names inTys) outTy
    let lam = foldr (\inTy body -> C.FunIntro inTy body) cBody cInTys
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
      Nothing -> errorTerm (UnboundVariable name)
  TermAst Univ -> do
    stage <- freshStageUV
    cStage <- readbackStage False stage
    pure (C.TypeType cStage, N.TypeType stage)
  TermAst (Let decls body) ->
    withDecls decls do
      cDecls <- traverse ED.check (declsIds decls)
      (cBody, bodyTy) <- infer body
      pure (C.Let cDecls cBody, bodyTy)
  TermAst (Rule outTy inTy) -> do
    cTerm <- C.FunType Implicit <$> checkMetaType inTy <*> checkMetaType outTy
    pure (cTerm, N.TypeType N.Meta)
  TermAst (IOType ty) -> do
    cTy <- checkObjectType ty
    pure (C.IOType cTy, N.TypeType (N.Object N.RepIntroPtr))
  TermAst (IOPure term) -> do
    ty <- freshTypeUV
    cTerm <- check term ty
    pure (C.IOIntroPure cTerm, N.IOType ty)
  TermAst (IOBind act k) -> do
    let inTy = opTy act
    outTy <- N.IOType <$> freshTypeUV
    outTyClo <- readbackWeak outTy >>= closureOf
    cK <- check k (N.FunType Explicit inTy outTyClo)
    pure (C.IOIntroBind act cK, outTy)
  TermAst UnitType -> pure (C.UnitType, N.TypeType (N.Object N.RepIntroErased))
  TermAst Unit -> pure (C.UnitIntro, N.UnitType)
  TermAst RepType -> pure (C.RepType, N.TypeType N.Meta)
  TermAst PtrRep -> pure (C.RepIntroPtr, N.RepType)
  TermAst LazyRep -> pure (C.RepIntroLazy, N.RepType)
  TermAst WordRep -> pure (C.RepIntroWord, N.RepType)
  TermAst (ProdRep rs) -> do
    cRs <- traverse (flip check N.RepType) rs
    pure (C.RepIntroProd cRs, N.RepType)
  TermAst (SumRep rs) -> do
    cRs <- traverse (flip check N.RepType) rs
    pure (C.RepIntroSum cRs, N.RepType)
  TermAst ErasedRep -> pure (C.RepIntroErased, N.RepType)

opTy :: IOOperation -> N.Term
opTy (PutChar _) = N.UnitType

checkType :: Elab sig m => TermAst -> m C.Term
checkType term = do
  stage <- freshStageUV
  check term (N.TypeType stage)

checkMetaType :: Elab sig m => TermAst -> m C.Term
checkMetaType term = check term (N.TypeType N.Meta)

checkObjectType :: Elab sig m => TermAst -> m C.Term
checkObjectType term = do
  rep <- freshTypeUV
  check term (N.TypeType (N.Object rep)) -- FIXME

declsIds :: [DeclarationAst] -> [Id]
declsIds = concatMap go where
  go :: DeclarationAst -> [Id]
  go (SourcePos decl _) = go decl
  go (DeclAst (Datatype _ _ constrs) did) = did : map unCId constrs
  go decl = [unId decl]
