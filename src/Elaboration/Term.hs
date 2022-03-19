module Elaboration.Term where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Extra hiding(unId)
import Elaboration.Effect
import Elaboration.Decl qualified as ED
import Control.Monad
import Normalization hiding(eval, readbackWeak)
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
  TermAst (MetaLam (map unName -> names) body) -> do
    inTys <- traverse (const freshTypeUV) names
    cInTys <- traverse readbackWeak inTys
    outTy <- freshTypeUV
    cOutTy <- readbackWeak outTy
    let ty = foldr (\inTy outTy -> C.MetaFunType Explicit inTy outTy) cOutTy (tail cInTys)
    vTy <- N.MetaFunType Explicit (head inTys) <$> closureOf ty
    cBody <- checkBody (zip names inTys) outTy
    let lam = foldr (\_ body -> C.MetaFunIntro body) cBody cInTys
    pure (lam, vTy)
    where
      checkBody :: Elab sig m => [(Name, N.Term)] -> N.Term -> m C.Term
      checkBody [] outTy = check body outTy
      checkBody ((name, inTy):params) outTy = bindLocal name inTy (checkBody params outTy)
  TermAst (ObjLam (map unName -> names) body) -> do
    inTys <- traverse (const freshTypeUV) names
    inTyReps <- traverse (const freshRepUV) names
    cInTys <- traverse readbackWeak inTys
    outTyReps <- traverse (const freshRepUV) names
    outTy <- freshTypeUV
    cOutTy <- readbackWeak outTy
    let ty = foldr (\(inTyRep, outTyRep, inTy) outTy -> C.ObjectFunType inTyRep inTy outTy outTyRep) cOutTy (zip3 (tail inTyReps) (tail outTyReps) (tail cInTys))
    vTy <- N.ObjectFunType (head inTyReps) (head inTys) <$> closureOf ty <*> pure (head outTyReps)
    cBody <- checkBody (zip names inTys) outTy
    let lam = foldr (\rep body -> C.ObjectFunIntro rep body) cBody inTyReps
    pure (lam, vTy)
    where
      checkBody :: Elab sig m => [(Name, N.Term)] -> N.Term -> m C.Term
      checkBody [] outTy = check body outTy
      checkBody ((name, inTy):params) outTy = bindLocal name inTy (checkBody params outTy)    
  TermAst (MetaPi (NameAst name) inTy outTy) -> do
    cInTy <- check inTy (N.TypeType Meta)
    vInTy <- eval cInTy
    cOutTy <- bindLocal name vInTy (check outTy (N.TypeType Meta))
    pure (C.MetaFunType Explicit cInTy cOutTy, N.TypeType Meta)
  TermAst (ObjPi (NameAst name) inTy outTy) -> do
    inTyRep <- freshRepUV
    cInTy <- check inTy (N.TypeType (Object inTyRep))
    vInTy <- eval cInTy
    outTyRep <- freshRepUV
    cOutTy <- bindLocal name vInTy (check outTy (N.TypeType (Object outTyRep)))
    pure (C.ObjectFunType inTyRep cInTy cOutTy outTyRep, N.TypeType (Object Ptr))
  TermAst (App lam args) -> do
    (cLam, lamTy) <- infer lam
    case lamTy of
      N.MetaFunType _ _ _ -> do
        (cArgs, outTy) <- checkArgsMeta args lamTy
        pure (foldl' (\lam arg -> C.MetaFunElim lam arg) cLam cArgs, outTy)
      N.ObjectFunType _ _ _ _ -> do
        (cArgs, outTy) <- checkArgsObject args lamTy
        pure (foldl' (\lam (arg, rep) -> C.ObjectFunElim lam arg rep) cLam cArgs, outTy)
    where
      checkArgsObject :: Elab sig m => [TermAst] -> N.Term -> m ([(C.Term, RuntimeRep)], N.Term)
      checkArgsObject [] outTy = pure ([], outTy)
      checkArgsObject (arg:args) (N.ObjectFunType _ inTy outTy rep) = do
        cArg <- check arg inTy
        vArg <- eval cArg
        (cArgs, outTy') <- appClosure outTy vArg >>= checkArgsObject args
        pure ((cArg, rep):cArgs, outTy')

      checkArgsMeta :: Elab sig m => [TermAst] -> N.Term -> m ([C.Term], N.Term)
      checkArgsMeta [] outTy = pure ([], outTy)
      checkArgsMeta (arg:args) (N.MetaFunType _ inTy outTy) = do
        cArg <- check arg inTy
        vArg <- eval cArg
        (cArgs, outTy') <- appClosure outTy vArg >>= checkArgsMeta args
        pure (cArg:cArgs, outTy')
  TermAst (Var name) -> do
    binding <- lookupBinding name
    case binding of
      Just (BLocal ix ty) -> pure (C.LocalVar ix, ty)
      Just (BGlobal did) -> do
        ty <- fst <$> ED.declType did >>= eval
        pure (C.GlobalVar did, ty)
      Nothing -> errorTerm (UnboundVariable name)
  TermAst Univ -> do
    -- stage <- freshStageUV
    pure (C.TypeType (Object Ptr), N.TypeType (Object Ptr))
  TermAst (Let decls body) ->
    withDecls decls do
      cDecls <- traverse ED.check (declsIds decls)
      (cBody, bodyTy) <- infer body
      pure (C.Let cDecls cBody, bodyTy)
  TermAst (Rule outTy inTy) -> do
    cTerm <- C.MetaFunType Implicit <$> checkMetaType' inTy <*> checkMetaType' outTy
    pure (cTerm, N.TypeType Meta)
  TermAst (IOType ty) -> do
    cTy <- checkObjectType' ty
    pure (C.IOType cTy, N.TypeType (Object Ptr))
  TermAst (IOPure term) -> do
    ty <- freshTypeUV
    cTerm <- check term ty
    pure (C.IOIntroPure cTerm, N.IOType ty)
  TermAst (IOBind act k) -> do
    let (inTy, rep) = opTy act
    outTy <- N.IOType <$> freshTypeUV
    outTyClo <- readbackWeak outTy >>= closureOf
    cK <- check k (N.ObjectFunType rep inTy outTyClo Ptr)
    pure (C.IOIntroBind act cK, outTy)
  TermAst UnitType -> pure (C.UnitType, N.TypeType (Object Erased))
  TermAst Unit -> pure (C.UnitIntro, N.UnitType)

opTy :: IOOperation -> (N.Term, RuntimeRep)
opTy (PutChar _) = (N.UnitType, Erased)

checkType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkType term = do
  stage <- freshStageUV
  (,) <$> check term (N.TypeType stage) <*> pure (N.TypeType stage)

checkMetaType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkMetaType term = (,) <$> check term (N.TypeType Meta) <*> pure (N.TypeType Meta)

checkMetaType' :: Elab sig m => TermAst -> m C.Term
checkMetaType' ty = fst <$> checkMetaType ty

checkObjectType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkObjectType term = do
  -- rep <- freshRepUV
  (,) <$> check term (N.TypeType (Object {-rep-}Ptr)) <*> pure (N.TypeType (Object {-rep-}Ptr)) -- FIXME

checkObjectType' :: Elab sig m => TermAst -> m C.Term
checkObjectType' ty = fst <$> checkObjectType ty

declsIds :: [DeclarationAst] -> [Id]
declsIds = concatMap go where
  go :: DeclarationAst -> [Id]
  go (SourcePos decl _) = go decl
  go (DeclAst (Datatype _ _ constrs) did) = did : map unCId constrs
  go decl = [unId decl]
