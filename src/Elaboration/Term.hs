module Elaboration.Term where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Extra hiding(unId)
import Extra
import Elaboration.Effect
import Elaboration.Decl qualified as ED
import Control.Monad
import Normalization hiding(eval, readback)
import Data.Foldable(foldl', foldr, foldrM)
import Debug.Trace
import Data.Sequence
import Prelude hiding(zip, concatMap, head, tail)

check :: Elab sig m => TermAst -> N.Term -> m C.Term
check term goal = do
  (cTerm, ty) <- infer term
  unify goal ty
  pure cTerm

infer :: Elab sig m => TermAst -> m (C.Term, N.Term)
infer term = case term of
  SourcePos term pos -> withPos pos (infer term)
  TermAst (MetaLam (fmap unName -> names) body) -> do
    inTys <- traverse (const freshTypeUV) names
    cInTys <- traverse readback inTys
    outTy <- freshTypeUV
    cOutTy <- readback outTy
    let ty = foldr (\inTy outTy -> C.MetaFunType Explicit inTy outTy) cOutTy (tail cInTys)
    vTy <- N.MetaFunType Explicit (head inTys) <$> closureOf ty
    cBody <- checkBody (zip names inTys) outTy
    let lam = foldr (\_ body -> C.MetaFunIntro body) cBody cInTys
    pure (lam, vTy)
    where
      checkBody :: Elab sig m => Seq (Name, N.Term) -> N.Term -> m C.Term
      checkBody Empty outTy = check body outTy
      checkBody ((name, inTy) :<| params) outTy = bindLocal name inTy (checkBody params outTy)
  TermAst (ObjLam (fmap unName -> names) body) -> do
    inTys <- traverse (const freshTypeUV) names
    cInTys <- traverse readback inTys
    outTy <- freshTypeUV
    cOutTy <- readback outTy
    let ty = foldr (\inTy outTy -> C.ObjectFunType inTy outTy) cOutTy (tail cInTys)
    vTy <- N.ObjectFunType (head inTys) <$> closureOf ty
    cBody <- checkBody (zip names inTys) outTy
    let lam = foldr (\_ body -> C.ObjectFunIntro body) cBody inTys
    pure (lam, vTy)
    where
      checkBody :: Elab sig m => Seq (Name, N.Term) -> N.Term -> m C.Term
      checkBody Empty outTy = check body outTy
      checkBody ((name, inTy) :<| params) outTy = bindLocal name inTy (checkBody params outTy)    
  TermAst (MetaPi (NameAst name) inTy outTy) -> do
    cInTy <- check inTy (N.TypeType Meta)
    vInTy <- eval cInTy
    cOutTy <- bindLocal name vInTy (check outTy (N.TypeType Meta))
    pure (C.MetaFunType Explicit cInTy cOutTy, N.TypeType Meta)
  TermAst (ObjPi (NameAst name) inTy outTy) -> do
    cInTy <- check inTy (N.TypeType Object)
    vInTy <- eval cInTy
    cOutTy <- bindLocal name vInTy (check outTy (N.TypeType Object))
    pure (C.ObjectFunType cInTy cOutTy, N.TypeType Object)
  TermAst (App lam args) -> do
    (cLam, lamTy) <- infer lam
    let
      elim = case lamTy of
        N.MetaFunType _ _ _ -> C.MetaFunElim
        N.ObjectFunType _ _ -> C.ObjectFunElim
    (cArgs, outTy) <- checkArgs args lamTy
    pure (foldl' (\lam arg -> elim lam arg) cLam cArgs, outTy)
    where
      checkArgs :: Elab sig m => Seq TermAst -> N.Term -> m (Seq C.Term, N.Term)
      checkArgs Empty outTy = pure (Empty, outTy)
      checkArgs (arg :<| args) (N.FunType inTy outTy) = do
        cArg <- check arg inTy
        vArg <- eval cArg
        (cArgs, outTy') <- appClosure outTy vArg >>= checkArgs args
        pure (cArg <| cArgs, outTy')
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
    pure (C.TypeType Object, N.TypeType Object)
  TermAst (Let decls body) ->
    withDecls decls do
      cDecls <- traverse ED.check (declsIds decls)
      (cBody, bodyTy) <- infer body
      pure (C.Let cDecls cBody, bodyTy)
  TermAst (Rule outTy inTy) -> do
    cTerm <- C.MetaFunType Implicit <$> checkMetaType' inTy <*> checkMetaType' outTy
    pure (cTerm, N.TypeType Meta)
  TermAst (LiftCore ty) -> do
    cTy <- checkObjectType' ty
    pure (C.CodeCoreType cTy, N.TypeType Meta)
  TermAst (QuoteCore term) -> do
    ty <- freshTypeUV
    cTerm <- check term ty
    pure (C.CodeCoreIntro cTerm, N.CodeCoreType ty)
  TermAst (SpliceCore quote) -> do
    ty <- freshTypeUV
    cQuote <- check quote (N.CodeCoreType ty)
    pure (C.CodeCoreElim cQuote, ty)
  TermAst (LiftLow ty) -> do
    cTy <- checkLowType' ty
    pure (C.CodeLowType cTy, N.TypeType Meta)
  TermAst (QuoteLow term) -> do
    ty <- freshTypeUV
    cTerm <- check term ty
    pure (C.CodeLowIntro cTerm, N.CodeLowType ty)
  TermAst (SpliceLow quote) -> do
    ty <- freshTypeUV
    cQuote <- check quote (N.CodeLowType ty)
    pure (C.CodeLowElim cQuote, ty)

checkType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkType term = do
  stage <- freshStageUV
  (,) <$> check term (N.TypeType stage) <*> pure (N.TypeType stage)

checkMetaType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkMetaType term = (,) <$> check term (N.TypeType Meta) <*> pure (N.TypeType Meta)

checkMetaType' :: Elab sig m => TermAst -> m C.Term
checkMetaType' ty = fst <$> checkMetaType ty

checkLowType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkLowType term = (,) <$> check term (N.TypeType Low) <*> pure (N.TypeType Low)

checkLowType' :: Elab sig m => TermAst -> m C.Term
checkLowType' ty = fst <$> checkLowType ty

checkObjectType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkObjectType term =
  (,) <$> check term (N.TypeType Object) <*> pure (N.TypeType Object) -- FIXME

checkObjectType' :: Elab sig m => TermAst -> m C.Term
checkObjectType' ty = fst <$> checkObjectType ty

declsIds :: Seq DeclarationAst -> Seq Id
declsIds = concatMap go where
  go :: DeclarationAst -> Seq Id
  go (SourcePos decl _) = go decl
  go (DeclAst (Datatype _ _ constrs) did) = did <| fmap unCId constrs
  go decl = singleton (unId decl)
