module Elaboration.Term where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Common hiding(unId, RigidTerm(..))
import Extra
import Elaboration.Effect
import Elaboration.Declaration qualified as ED
import Elaboration.CStatement qualified as ES
import Control.Monad
import Normalization hiding(eval, readback)
import Data.Foldable(foldl', foldr, foldrM)
import Debug.Trace
import Data.Sequence
import Prelude hiding(zip, concatMap, head, tail, length)

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
    let ty = foldr (\inTy outTy -> C.MetaFunType inTy outTy) cOutTy (tail cInTys)
    vTy <- N.MetaFunType (head inTys) <$> closureOf ty
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
    let ty = foldr (\inTy outTy -> C.ObjFunType inTy outTy) cOutTy (tail cInTys)
    vTy <- N.ObjFunType (head inTys) <$> closureOf ty
    cBody <- checkBody (zip names inTys) outTy
    let lam = foldr (\_ body -> C.ObjFunIntro body) cBody inTys
    pure (lam, vTy)
    where
      checkBody :: Elab sig m => Seq (Name, N.Term) -> N.Term -> m C.Term
      checkBody Empty outTy = check body outTy
      checkBody ((name, inTy) :<| params) outTy = bindLocal name inTy (checkBody params outTy)    
  TermAst (MetaPi (NameAst name) inTy outTy) -> do
    cInTy <- check inTy (N.TypeType N.Meta)
    vInTy <- eval cInTy
    cOutTy <- bindLocal name vInTy (check outTy (N.TypeType N.Meta))
    pure (C.MetaFunType cInTy cOutTy, N.TypeType N.Meta)
  TermAst (ObjPi (NameAst name) inTy outTy) -> do
    cInTy <- check inTy (N.TypeType N.Obj)
    vInTy <- eval cInTy
    cOutTy <- bindLocal name vInTy (check outTy (N.TypeType N.Obj))
    pure (C.ObjFunType cInTy cOutTy, N.TypeType N.Obj)
  TermAst (App lam args) -> do
    (cLam, lamTy) <- infer lam
    let
      elim = case lamTy of
        N.MetaFunType _ _ -> C.MetaFunElim
        N.ObjFunType _ _ -> C.ObjFunElim
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
  TermAst OUniv -> pure (C.TypeType C.Obj, N.TypeType N.Obj)
  TermAst MUniv -> pure (C.TypeType C.Meta, N.TypeType N.Meta)
  TermAst LCUniv -> pure (C.TypeType (C.Low C), N.TypeType N.Meta)
  TermAst (Let decls body) ->
    withDecls decls do
      cDecls <- traverse ED.check (declsIds decls)
      (cBody, bodyTy) <- infer body
      pure (C.Let cDecls cBody, bodyTy)
  TermAst (LiftCore ty) -> do
    cTy <- checkObjType' ty
    pure (C.Rigid (C.CodeCoreType cTy), N.TypeType N.Meta)
  TermAst (QuoteCore term) -> do
    ty <- freshTypeUV
    cTerm <- check term ty
    pure (C.Rigid (C.CodeCoreIntro cTerm), N.Rigid (N.CodeCoreType ty))
  TermAst (SpliceCore quote) -> do
    ty <- freshTypeUV
    cQuote <- check quote (N.Rigid (N.CodeCoreType ty))
    pure (C.CodeCoreElim cQuote, ty)
  TermAst (LiftLowCTm ty) -> do
    cTy <- checkLowCType' ty
    pure (C.Rigid (C.CodeLowCTmType cTy), N.TypeType N.Meta)
  TermAst (QuoteLowCTm term) -> do
    ty <- freshTypeUV
    cTerm <- check term ty
    pure (C.Rigid (C.CodeLowCTmIntro cTerm), N.Rigid (N.CodeLowCTmType ty))
  TermAst (SpliceLowCTm quote) -> do
    ty <- freshTypeUV
    cQuote <- check quote (N.Rigid (N.CodeLowCTmType ty))
    pure (C.CodeLowCTmElim cQuote, ty)
  TermAst (LiftLowCStmt ty) -> do
    cTy <- checkLowCType' ty
    pure (C.Rigid (C.CodeLowCStmtType cTy), N.TypeType N.Meta)
  TermAst (QuoteLowCStmt stmt) -> do
    (cStmt, retTy) <- ES.infer stmt
    pure (C.Rigid (C.CodeLowCStmtIntro cStmt), N.Rigid (N.CodeLowCStmtType retTy))
  TermAst (CPtrType ty) -> do
    cTy <- checkLowCType' ty
    pure (C.Rigid (C.CPtrType cTy), N.TypeType (N.Low C))
  TermAst CIntType -> pure (C.Rigid C.CIntType, N.TypeType (N.Low C))
  TermAst CVoidType -> pure (C.Rigid C.CVoidType, N.TypeType (N.Low C))
  -- TermAst (CLValType ty) -> do
  --   cTy <- checkLowCType' ty
  --   pure (C.CLValType cTy, N.TypeType (N.Low C))
  -- TermAst (CRValType ty) -> do
  --   cTy <- checkLowCType' ty
  --   pure (C.CRValType cTy, N.TypeType (N.Low C))
  TermAst (CRef term) -> do
    ty <- freshTypeUV
    cTerm <- check term ty
    pure (C.Rigid (C.COp (Ref cTerm)), N.Rigid (N.CPtrType ty))
  TermAst (CDeref term) -> do
    ty <- freshTypeUV
    -- vc <- freshVCUV
    cTerm <- check term (N.Rigid (N.CPtrType ty))
    pure (C.Rigid (C.COp (Deref cTerm)), ty)
  TermAst (CAdd term1 term2) -> do
    cTerm1 <- check term1 (N.Rigid N.CIntType)
    cTerm2 <- check term2 (N.Rigid N.CIntType)
    pure (C.Rigid (C.COp (Add cTerm1 cTerm2)), N.Rigid N.CIntType)
  TermAst (CSub term1 term2) -> do
    cTerm1 <- check term1 (N.Rigid N.CIntType)
    cTerm2 <- check term2 (N.Rigid N.CIntType)
    pure (C.Rigid (C.COp (Sub cTerm1 cTerm2)), N.Rigid N.CIntType)
  TermAst (CLess term1 term2) -> do
    cTerm1 <- check term1 (N.Rigid N.CIntType)
    cTerm2 <- check term2 (N.Rigid N.CIntType)
    pure (C.Rigid (C.COp (Less cTerm1 cTerm2)), N.Rigid N.CIntType)
  TermAst (CGrtr term1 term2) -> do
    cTerm1 <- check term1 (N.Rigid N.CIntType)
    cTerm2 <- check term2 (N.Rigid N.CIntType)
    pure (C.Rigid (C.COp (Grtr cTerm1 cTerm2)), N.Rigid N.CIntType)
  TermAst (CEql term1 term2) -> do
    cTerm1 <- check term1 (N.Rigid N.CIntType)
    cTerm2 <- check term2 (N.Rigid N.CIntType)
    pure (C.Rigid (C.COp (Eql cTerm1 cTerm2)), N.Rigid N.CIntType)
  TermAst (CFunCall fn args) -> do
    (cFn, fnTy) <- infer fn
    r <- go fnTy
    case r of
      Just (inTys, outTy) | length inTys == length args -> do
        cArgs <- traverse (\(arg, inTy) -> check arg inTy) (zip args inTys)
        pure (C.Rigid (C.CFunCall cFn cArgs), outTy)
      Just (inTys, _) ->
        errorTerm (WrongAppArity (fromIntegral (length inTys)) (fromIntegral (length args)))
      Nothing -> errorTerm (ExpectedCFunType fnTy)
    where
      go :: Norm sig m => N.Term -> m (Maybe (Seq N.Term, N.Term))
      go (N.Rigid (N.CFunType inTys outTy)) = pure (Just (inTys, outTy))
      go (N.Neutral term _) = do
        term <- force term
        case term of
          Just term -> go term
          Nothing -> pure Nothing
      go _ = pure Nothing
  TermAst (CFunType inTys outTy) -> do
    cTerm <- C.Rigid <$> (C.CFunType <$> traverse (flip check (N.TypeType (N.Low C))) inTys <*> check outTy (N.TypeType (N.Low C)))
    pure (cTerm, N.TypeType (N.Low C))
  TermAst (CInt x) -> pure (C.Rigid (C.CIntIntro x), N.Rigid N.CIntType)
  TermAst (ImplProp p q) -> do
    cP <- check p (N.TypeType N.Meta)
    cQ <- check q (N.TypeType N.Meta)
    pure (C.Rigid (C.ImplType cP cQ), N.TypeType N.Meta)
  TermAst (ConjProp p q) -> do
    cP <- check p (N.TypeType N.Meta)
    cQ <- check q (N.TypeType N.Meta)
    pure (C.Rigid (C.ConjType cP cQ), N.TypeType N.Meta)
  TermAst (DisjProp p q) -> do
    cP <- check p (N.TypeType N.Meta)
    cQ <- check q (N.TypeType N.Meta)
    pure (C.Rigid (C.DisjType cP cQ), N.TypeType N.Meta)
  TermAst (ForallProp body) -> do
    inTy <- freshTypeUV
    outTy <- closureOf (C.TypeType C.Meta)
    cBody <- check body (N.MetaFunType inTy outTy)
    pure (C.Rigid (C.AllType cBody), N.TypeType N.Meta)
  TermAst (ExistsProp body) -> do
    inTy <- freshTypeUV
    outTy <- closureOf (C.TypeType C.Meta)
    cBody <- check body (N.MetaFunType inTy outTy)
    pure (C.Rigid (C.SomeType cBody), N.TypeType N.Meta)
  TermAst (EqualProp x y) -> do
    ty <- freshTypeUV
    cX <- check x ty
    cY <- check y ty
    pure (C.Rigid (C.PropIdType cX cY), N.TypeType N.Meta)
  TermAst Bool -> pure (C.Rigid C.TwoType, N.TypeType N.Obj)
  TermAst BTrue -> pure (C.Rigid C.TwoIntro0, N.Rigid N.TwoType)
  TermAst BFalse -> pure (C.Rigid C.TwoIntro1, N.Rigid N.TwoType)
  TermAst (Case scr ty body1 body2) -> do
    cScr <- check scr (N.Rigid N.TwoType)
    vScr <- eval cScr
    case ty of
      Just (NameAst name, ty) -> do
        cTy <- bindLocal name (N.Rigid N.TwoType) (check ty (N.TypeType N.Obj))
        vTy <- define vScr (eval cTy)
        vTy1 <- define (N.Rigid N.TwoIntro0) (eval cTy)
        vTy2 <- define (N.Rigid N.TwoIntro1) (eval cTy)
        cBody1 <- check body1 vTy1
        cBody2 <- check body2 vTy2
        pure (C.TwoElim cScr cTy cBody1 cBody2, vTy)
      Nothing -> do
        vTy <- freshTypeUV
        cTy <- readback vTy
        cBody1 <- check body1 vTy
        cBody2 <- check body2 vTy
        pure (C.TwoElim cScr cTy cBody1 cBody2, vTy)
  TermAst (Sigma ty1 (NameAst name) ty2) -> do
    cTy1 <- check ty1 (N.TypeType N.Obj)
    vTy1 <- eval cTy1
    cTy2 <- bindLocal name vTy1 (check ty2 (N.TypeType N.Obj))
    pure (C.Rigid (C.SigmaType cTy1 cTy2), N.TypeType N.Obj)
  TermAst (Pair prj1 prj2) -> do
    ty1 <- freshTypeUV
    cPrj1 <- check prj1 ty1
    ty2 <- freshTypeUV
    cPrj2 <- check prj2 ty2
    pure (C.Rigid (C.SigmaIntro cPrj1 cPrj2), N.Rigid (N.SigmaType ty1 ty2))
  TermAst (Split scr ty body) -> do
    scrTy <- N.Rigid <$> (N.SigmaType <$> freshTypeUV <*> freshTypeUV)
    cScr <- check scr scrTy
    vScr <- eval cScr
    vTy <- case ty of
      Just (NameAst name, ty) -> do
        cTy <- bindLocal name scrTy (check ty (N.TypeType N.Obj))
        define vScr (eval cTy)
      Nothing -> freshTypeUV
    cTy <- readback vTy
    cBody <- check body vTy
    pure (C.SigmaElim cScr cTy cBody, vTy)
  TermAst (Singleton term) -> do
    cTerm <- freshTypeUV >>= check term
    pure (C.Rigid (C.SingType cTerm), N.TypeType N.Obj)
  TermAst Sing -> do
    term <- freshTypeUV
    cTerm <- readback term
    pure (C.Rigid (C.SingIntro cTerm), N.Rigid (N.SingType term))
  TermAst (Equal term1 term2) -> do
    cTerm1 <- freshTypeUV >>= check term1
    cTerm2 <- freshTypeUV >>= check term2
    pure (C.Rigid (C.ObjIdType cTerm1 cTerm2), N.TypeType N.Obj)
  TermAst Refl -> do
    term <- freshTypeUV
    cTerm <- readback term
    pure (C.Rigid (C.ObjIdIntro cTerm), N.Rigid (N.ObjIdType term term))

checkMetaType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkMetaType term = (,) <$> check term (N.TypeType N.Meta) <*> pure (N.TypeType N.Meta)

checkMetaType' :: Elab sig m => TermAst -> m C.Term
checkMetaType' ty = fst <$> checkMetaType ty

checkLowCType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkLowCType term = (,) <$> check term (N.TypeType (N.Low C)) <*> pure (N.TypeType (N.Low C))

checkLowCType' :: Elab sig m => TermAst -> m C.Term
checkLowCType' ty = fst <$> checkLowCType ty

checkObjType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkObjType term =
  (,) <$> check term (N.TypeType N.Obj) <*> pure (N.TypeType N.Obj) -- FIXME

checkObjType' :: Elab sig m => TermAst -> m C.Term
checkObjType' ty = fst <$> checkObjType ty

declsIds :: Seq DeclarationAst -> Seq Id
declsIds = concatMap go where
  go :: DeclarationAst -> Seq Id
  go (SourcePos decl _) = go decl
  go decl = singleton (unId decl)
