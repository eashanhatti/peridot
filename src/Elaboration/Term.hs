module Elaboration.Term where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Quote qualified as Q
import Syntax.Semantic qualified as N
import Syntax.Extra hiding(unId)
import Elaboration.Effect
import Elaboration.Decl qualified as ED
import Control.Monad
import Normalization hiding(eval, readbackWeak, readback)
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
    cInTys <- traverse readbackWeak inTys
    outTy <- freshTypeUV
    cOutTy <- readbackWeak outTy
    let ty = foldr (\inTy outTy -> C.ObjectFunType inTy outTy) cOutTy (tail cInTys)
    vTy <- N.ObjectFunType (head inTys) <$> closureOf ty
    cBody <- checkBody (zip names inTys) outTy
    let lam = foldr (\_ body -> C.ObjectFunIntro body) cBody inTys
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
      checkArgs :: Elab sig m => [TermAst] -> N.Term -> m ([C.Term], N.Term)
      checkArgs [] outTy = pure ([], outTy)
      checkArgs (arg:args) (N.FunType inTy outTy) = do
        cArg <- check arg inTy
        vArg <- eval cArg
        (cArgs, outTy') <- appClosure outTy vArg >>= checkArgs args
        pure (cArg:cArgs, outTy')
  TermAst (Var name) -> do
    binding <- lookupBinding name
    case binding of
      Just (BLocal ix ty) -> pure (C.LocalVar ix, ty)
      Just (BGlobal did) -> do
        ty <- fst <$> ED.declType did >>= eval
        pure (C.GlobalVar did, ty)
      Nothing -> errorTerm (UnboundVariable name)
  TermAst ObjUniv -> pure (C.TypeType Object, N.TypeType Object)
  TermAst MetaUniv -> pure (C.TypeType Meta, N.TypeType Meta)
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
    pure (C.IOType cTy, N.TypeType Object)
  TermAst (IOPure term) -> do
    ty <- freshTypeUV
    cTerm <- check term ty
    pure (C.IOIntroPure cTerm, N.IOType ty)
  TermAst (IOBind act k) -> do
    let inTy = opTy act
    outTy <- N.IOType <$> freshTypeUV
    outTyClo <- readbackWeak outTy >>= closureOf
    cK <- check k (N.ObjectFunType inTy outTyClo)
    pure (C.IOIntroBind act cK, outTy)
  TermAst UnitType -> pure (C.UnitType, N.TypeType Object)
  TermAst Unit -> pure (C.UnitIntro, N.UnitType)
  TermAst (Quote quote) -> do
    (cQuote, ty) <- inferQuote quote
    pure (C.QuoteIntro cQuote, N.QuoteType (N.QuoteIntro ty))
  TermAst (QuoteType ty) -> do
    cTy <- check ty (N.QuoteType (N.QuoteIntro Q.TypeType))
    pure (C.QuoteType cTy, N.TypeType Meta)

inferQuote :: Elab sig m => TermQuote -> m (C.TermQuote, N.TermQuote)
inferQuote (QPi inTy outTy) = do
  cInTy <- check inTy ((N.QuoteType . N.QuoteIntro) Q.TypeType)
  vInTy <- eval cInTy
  outKiClo <- freshTypeUV >>= readbackWeak >>= closureOf
  cOutTy <- check outTy (N.MetaFunType Explicit vInTy outKiClo)
  pure (Q.FunType cInTy cOutTy, Q.TypeType)
inferQuote (QLam body) = do
  inTy <- freshQTypeUV
  outTy <- freshQTypeUV
  outTyClo <- readbackWeak (N.QuoteIntro outTy) >>= closureOf
  cBody <- check body (N.MetaFunType Explicit (N.QuoteIntro inTy) outTyClo)
  pure (Q.FunIntro cBody, outTy)
inferQuote (QApp lam arg) = do
  (cLam, lamTy) <- infer lam
  inTy <- freshQTypeUV
  outTy <- freshQTypeUV
  unify ((N.QuoteType . N.QuoteIntro) (Q.FunType ((N.QuoteType . N.QuoteIntro) inTy) ((N.QuoteType . N.QuoteIntro) outTy))) lamTy
  cArg <- check arg ((N.QuoteType . N.QuoteIntro) inTy)
  pure (Q.FunElim cLam cArg, outTy)
inferQuote (QIOType ty) = do
  cTy <- check ty ((N.QuoteType . N.QuoteIntro) Q.TypeType)
  pure (Q.IOType cTy, Q.TypeType)
inferQuote (QIOPure term) = do
  ty <- freshQTypeUV
  cTerm <- check term ((N.QuoteType . N.QuoteIntro) ty)
  pure (Q.IOIntroPure cTerm, Q.IOType ((N.QuoteType . N.QuoteIntro) ty))
inferQuote (QIOBind act k) = do
  let inTy = opQTy act
  outTy <- freshQTypeUV
  cK <- check k ((N.QuoteType . N.QuoteIntro) (Q.FunType ((N.QuoteType . N.QuoteIntro) inTy) ((N.QuoteType . N.QuoteIntro) outTy)))
  pure (Q.IOIntroBind act cK, outTy)
inferQuote QUnitType = pure (Q.UnitType, Q.TypeType)
inferQuote QUnit = pure (Q.UnitIntro, Q.UnitType)
inferQuote QUniv = pure (Q.TypeType, Q.TypeType)
inferQuote QWorldType = pure (Q.WorldType, Q.UnqTypeType)
-- inferQuote (QVar (NameAst name)) = do
--   binding <- lookupBinding name
--   uv <- freshQTypeUV
--   case binding of
--     Just (BLocal ix ty) -> do
--       unify ty ((N.QuoteType . N.QuoteIntro) uv)
--       pure (Q.LocalVar ix, uv)
--     Just (BGlobal did) -> do
--       ty <- fst <$> ED.declType did >>= eval
--       unify ty ((N.QuoteType . N.QuoteIntro) uv)
--       pure (Q.GlobalVar did, uv)
--     Nothing -> errorQTerm (UnboundVariable name)
inferQuote (QLet _ _) = undefined -- FIXME
inferQuote QInstType = pure (Q.InstType, Q.TypeType)
inferQuote (QPrintChar char world cont) = do
  let inTy = ((N.QuoteType . N.QuoteIntro) Q.WorldType)
  cWorld <- check world inTy
  outTy <- closureOf ((C.QuoteType . C.QuoteIntro) Q.InstType)
  -- TODO: `world` linearity check
  cCont <- check cont (N.MetaFunType Explicit inTy outTy)
  pure (Q.InstIntroPrintChar char cWorld cCont, Q.InstType)
inferQuote (QStackAllocWord word world cont) = do
  let inTy1 = (N.QuoteType . N.QuoteIntro) Q.WordType
  let inTy2 = (N.QuoteType . N.QuoteIntro) Q.WorldType
  let cInTy2 = (C.QuoteType . C.QuoteIntro) Q.WorldType
  cWord <- check word inTy1
  cWorld <- check world inTy2
  outTy <- closureOf (C.MetaFunType Explicit cInTy2 ((C.QuoteType . C.QuoteIntro) Q.InstType))
  -- TODO: `world` linearity check
  cCont <- check cont (N.MetaFunType Explicit inTy1 outTy)
  pure (Q.InstIntroStackAllocWord cWord cWorld cCont, Q.InstType)
inferQuote (QStackPopWord world cont) = do
  let inTy = ((N.QuoteType . N.QuoteIntro) Q.WorldType)
  cWorld <- check world inTy
  outTy <- closureOf ((C.QuoteType . C.QuoteIntro) Q.InstType)
  -- TODO: `world` linearity check
  cCont <- check cont (N.MetaFunType Explicit inTy outTy)
  pure (Q.InstIntroStackPopWord cWorld cCont, Q.InstType)
inferQuote (QJump block args) = do
  (cArgs, argTys) <- unzip <$> traverse infer args
  let blockTy = (N.QuoteType . N.QuoteIntro) (Q.BasicBlockType argTys)
  cBlock <- check block blockTy
  pure (Q.InstIntroJump cBlock cArgs, Q.InstType)
inferQuote (QBasicBlockType tys) = do
  cTys <- traverse (flip check ((N.QuoteType . N.QuoteIntro) Q.InstType)) tys
  pure (Q.BasicBlockType cTys, Q.InstType)
inferQuote (QBasicBlock inst) = do
  ty <- freshTypeUV
  cInst <- check inst ty
  tys <- checkForm ty
  pure (Q.BasicBlockIntro cInst, Q.BasicBlockType tys)
  where
    checkForm :: Elab sig m => N.Term -> m [N.Term]
    checkForm ty = do
      inTy <- freshTypeUV
      outTy <- freshTypeUV >>= readbackWeak >>= closureOf
      b <- convertible ty (N.MetaFunType Explicit inTy outTy)
      if b then do
        unify (N.MetaFunType Explicit inTy outTy) ty
        inTys <- evalClosure outTy >>= checkForm
        pure (inTy:inTys)
      else do
        unify ((N.QuoteType . N.QuoteIntro) Q.InstType) ty
        pure []

opTy :: IOOperation -> N.Term
opTy (PutChar _) = N.UnitType

opQTy :: IOOperation -> N.TermQuote
opQTy (PutChar _) = Q.UnitType

checkType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkType term = do
  stage <- freshStageUV
  (,) <$> check term (N.TypeType stage) <*> pure (N.TypeType stage)

checkType' :: Elab sig m => TermAst -> m C.Term
checkType' ty = fst <$> checkType ty

checkMetaType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkMetaType term = (,) <$> check term (N.TypeType Meta) <*> pure (N.TypeType Meta)

checkMetaType' :: Elab sig m => TermAst -> m C.Term
checkMetaType' ty = fst <$> checkMetaType ty

checkObjectType :: Elab sig m => TermAst -> m (C.Term, N.Term)
checkObjectType term =
  (,) <$> check term (N.TypeType Object) <*> pure (N.TypeType Object)

checkObjectType' :: Elab sig m => TermAst -> m C.Term
checkObjectType' ty = fst <$> checkObjectType ty

declsIds :: [DeclarationAst] -> [Id]
declsIds = concatMap go where
  go :: DeclarationAst -> [Id]
  go (SourcePos decl _) = go decl
  go (DeclAst (Datatype _ _ constrs) did) = did : map unCId constrs
  go decl = [unId decl]
