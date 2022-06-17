module Elaboration.Term where

import Control.Effect.Reader
import Control.Effect.State
import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Common hiding(unId, RigidTerm(..))
import Data.Set(Set)
import Data.Set qualified as Set
import Data.Map(Map)
import Data.Map qualified as Map
import Data.Some
import Extra
import Elaboration.Effect
import Elaboration.Declaration qualified as ED
import Control.Monad
import Normalization hiding(eval, readback, zonk)
import Data.Foldable(foldl', foldr, foldrM, find, toList)
import Debug.Trace
import Data.Sequence
import Prelude hiding(zip, concatMap, head, tail, length, unzip)
import Shower
import Data.Bifunctor

check :: Elab sig m => TermAst -> N.Term -> m C.Term
check (SourcePos term pos) goal = withPos pos (check term goal)
check (TermAst (ObjLam (fmap (second unName) -> names) body)) goal =
  checkBody names goal
  where
    checkBody :: Elab sig m => Seq (PassMethod, Name) -> N.Term -> m C.Term
    checkBody Empty outTy@(N.viewFunType -> Nothing) = check body outTy
    checkBody names (N.Neutral ty redex) = do
      ty <- force ty
      case ty of
        Just ty -> checkBody names ty
        Nothing -> error $ shower (names, redex)
    checkBody ((pm1, name) :<| names) (N.ObjFunType pm2 inTy outTy)
      | pm1 == pm2
      = do
        vOutTy <- evalClosure outTy
        C.ObjFunIntro <$> bindLocal name inTy (checkBody names vOutTy)
    checkBody names (N.ObjFunType Unification inTy outTy) = do
      vOutTy <- evalClosure outTy
      C.ObjFunIntro <$> bind (checkBody names vOutTy)
    checkBody names ty = do
      cTy <- readback ty
      report (InferredFunType cTy)
      pure (C.Rigid C.ElabError)
check term@(TermAst (Struct defs)) goal = do
  goal <- unfold goal
  case goal of
    N.RecType tys -> do
      cDefs <- go Empty defs tys
      pure (C.RecIntro cDefs)
    _ -> checkBase term goal
  where
    go ::
      Elab sig m =>
      Seq N.Term ->
      Seq (NameAst, TermAst) ->
      Seq (Field, N.Closure) ->
      m (Seq (Field, C.Term))
    go vDefs ((NameAst name, def) :<| defs) ((fd, ty) :<| tys) = do
      when (nameToField name /= fd) (error "TODO")
      vTy <- appClosureN ty vDefs
      cDef <- check def vTy
      vDef <- eval cDef
      cDefs <- defineLocal name vTy vDef (go (vDef <| vDefs) defs tys)
      pure ((fd, cDef) <| cDefs) 
    go _ Empty Empty = pure Empty
    go _ _ _ = error "TODO"
check (TermAst (Case scr body1 body2)) goal = do
  cScr <- check scr (N.Rigid N.TwoType)
  vScr <- eval cScr
  cGoal <- readback goal
  goal1 <- bindDefEq vScr (N.Rigid N.TwoIntro0) (eval cGoal)
  goal2 <- bindDefEq vScr (N.Rigid N.TwoIntro1) (eval cGoal)
  cBody1 <- bindDefEq vScr (N.Rigid N.TwoIntro0) (check body1 goal1)
  cBody2 <- bindDefEq vScr (N.Rigid N.TwoIntro1) (check body2 goal2)
  pure (C.TwoElim cScr cBody1 cBody2)
check term goal = checkBase term goal

checkBase :: Elab sig m => TermAst -> N.Term -> m C.Term
checkBase term goal = do
  (cTerm, ty) <- infer term
  cTerm' <- unify cTerm goal ty
  pure cTerm'

infer :: Elab sig m => TermAst -> m (C.Term, N.Term)
infer term = case term of
  SourcePos term pos -> withPos pos (infer term)
  TermAst (MetaLam (fmap unName -> names) body) -> do
    inTys <- traverse (const freshTypeUV) names
    cInTys <- traverse readback inTys
    outTy <- freshTypeUV
    cOutTy <- readback outTy
    let
      ty =
        foldr
          (\inTy outTy -> C.MetaFunType Explicit inTy outTy)
          cOutTy
          (tail cInTys)
    vTy <- N.MetaFunType Explicit (head inTys) <$> closureOf ty
    cBody <- checkBody (zip names inTys) outTy
    let lam = foldr (\_ body -> C.MetaFunIntro body) cBody cInTys
    pure (lam, vTy)
    where
      checkBody :: Elab sig m => Seq (Name, N.Term) -> N.Term -> m C.Term
      checkBody Empty outTy = check body outTy
      checkBody ((name, inTy) :<| params) outTy =
        bindLocal name inTy (checkBody params outTy)
  TermAst (ObjLam (fmap (second unName) -> names) body) -> do
    inTys <- traverse (const freshTypeUV) names
    cInTys <- traverse readback inTys
    outTy <- freshTypeUV
    cOutTy <- readback outTy
    let
      ty =
        foldr
          (\(pm, inTy) outTy -> C.ObjFunType pm inTy outTy)
          cOutTy
          (zip (fmap fst names) (tail cInTys))
    vTy <- N.ObjFunType (fst (head names)) (head inTys) <$> closureOf ty
    cBody <- checkBody (zip (fmap snd names) inTys) outTy
    let lam = foldr (\_ body -> C.ObjFunIntro body) cBody inTys
    pure (lam, vTy)
    where
      checkBody :: Elab sig m => Seq (Name, N.Term) -> N.Term -> m C.Term
      checkBody Empty outTy = check body outTy
      checkBody ((name, inTy) :<| params) outTy =
        bindLocal name inTy (checkBody params outTy)    
  TermAst (MetaPi pm (NameAst name) inTy outTy) -> do
    cInTy <- check inTy (N.MetaTypeType)
    vInTy <- eval cInTy
    cOutTy <- bindLocal name vInTy (check outTy (N.MetaTypeType))
    pure (C.MetaFunType pm cInTy cOutTy, N.MetaTypeType)
  TermAst (ObjPi pm (NameAst name) inTy outTy) -> do
    cInTy <- check inTy (N.ObjTypeType)
    vInTy <- eval cInTy
    cOutTy <- bindLocal name vInTy (check outTy (N.ObjTypeType))
    pure (C.ObjFunType pm cInTy cOutTy, N.ObjTypeType)
  TermAst (App lam args) -> do
    (cLam, lamTy) <- infer lam
    r <- scopeUVState do
      x <- freshTypeUV
      y <- freshTypeUV >>= readback >>= closureOf
      (||) <$> -- FIXME: Kind of a hack
        convertible (N.ObjFunType Explicit x y) lamTy <*>
        convertible (N.ObjFunType Unification x y) lamTy
    let elim = if r then C.ObjFunElim else C.MetaFunElim
    (cArgs, outTy) <- checkArgs args lamTy
    pure (foldl' (\lam arg -> elim lam arg) cLam cArgs, outTy)
    where
      checkArgs ::
        Elab sig m =>
        Seq (PassMethod, TermAst) ->
        N.Term ->
        m (Seq C.Term, N.Term)
      checkArgs Empty outTy@(N.viewFunType -> Nothing) = pure (Empty, outTy)
      checkArgs args (N.Neutral ty redex) = do
        ty <- force ty
        case ty of
          Just ty -> checkArgs args ty
          Nothing -> error $ shower redex
      checkArgs ((pm1, arg) :<| args) (N.FunType pm2 inTy outTy)
        | pm1 == pm2
        = do
          cArg <- check arg inTy
          vArg <- eval cArg
          (cArgs, outTy') <- appClosure outTy vArg >>= checkArgs args
          pure (cArg <| cArgs, outTy')
      checkArgs args (N.FunType Unification inTy outTy) = do
        arg <- freshTypeUV
        cArg <- readback arg
        (cArgs, outTy') <- appClosure outTy arg >>= checkArgs args
        pure (cArg <| cArgs, outTy')
      checkArgs args ty = error "TODO: Error reporting"
  TermAst (Var name) -> do
    binding <- lookupBinding name
    case binding of
      Just (BLocal ix ty) -> pure (C.LocalVar ix, ty)
      Just (BGlobal did) -> do
        isType <- unIsType <$> ask
        (ty, univ) <- ED.declType did
        vTy <- eval ty
        when isType (void (ED.check did))
        pure (C.GlobalVar (C.Rigid (C.RNameIntro name univ did)), vTy)
      Nothing -> errorTerm (UnboundVariable name)
  TermAst OUniv -> pure (C.ObjTypeType, N.ObjTypeType)
  TermAst MUniv -> pure (C.MetaTypeType, N.MetaTypeType)
  TermAst (Let decls body) ->
    withDecls decls do
      cDecls <-
        Map.fromList . toList <$> traverse
          (\did -> (did ,) <$> ED.check did)
          (declsIds decls)
      cDeclTys <-
        Map.fromList . toList <$> traverse
          (\did -> (did ,) <$> ED.declType did)
          (declsIds decls)
      graph <- unDepGraph <$> get
      (cBody, bodyTy) <- infer body
      let
        ordering ::
          Set (Some Key) ->
          Seq (Set (Some Key))
        ordering available =
          if available == Map.keysSet graph then
            mempty
          else
            let
              nowAvailable =
                Map.keysSet .
                Map.filter (\ds -> ds `Set.isSubsetOf` available) $
                graph
            in
              (<|)
                (nowAvailable `Set.difference` available)
                (ordering (nowAvailable <> available))
        construct :: Seq (Set (Some Key)) -> C.Term
        construct Empty = cBody
        construct (keys :<| order) =
          let cont = construct order
          in
            foldr
              (\key acc -> case key of
                Some (CheckDecl did) ->
                  C.Define
                    (C.Rigid (C.RNameIntro (UserName "<PLACEHOLDER>") (snd (cDeclTys Map.! did)) did))
                    (cDecls Map.! did)
                    acc
                Some (DeclType did) ->
                  C.Declare
                    (snd (cDeclTys Map.! did))
                    (C.Rigid (C.RNameIntro (UserName "<PLACEHOLDER>") (snd (cDeclTys Map.! did)) did))
                    (fst (cDeclTys Map.! did))
                    acc)
              cont
              keys
      let order = ordering mempty
      pure (construct order, bodyTy)
  TermAst (LiftObj ty) -> do
    cTy <- checkObjType' ty
    pure (C.Rigid (C.CodeObjType cTy), N.MetaTypeType)
  TermAst (QuoteObj term) -> do
    ty <- freshTypeUV
    cTerm <- check term ty
    pure (C.Rigid (C.CodeObjIntro cTerm), N.Rigid (N.CodeObjType ty))
  TermAst (SpliceObj quote) -> do
    ty <- freshTypeUV
    cQuote <- check quote (N.Rigid (N.CodeObjType ty))
    pure (C.CodeObjElim cQuote, ty)
  TermAst (LiftC ty) -> do
    cTy <- check ty N.LowCTypeType
    pure (C.Rigid (C.CodeCType cTy), N.MetaTypeType)
  TermAst (QuoteC term) -> do
    ty <- freshTypeUV
    cTerm <- check term ty
    pure (C.Rigid (C.CodeCIntro cTerm), N.Rigid (N.CodeCType ty))
  TermAst (SpliceC quote) -> do
    ty <- freshTypeUV
    cQuote <- check quote (N.Rigid (N.CodeCType ty))
    pure (C.CodeCElim cQuote, ty)
  TermAst (ImplProp p q) -> do
    cP <- check p (N.MetaTypeType)
    cQ <- check q (N.MetaTypeType)
    pure (C.Rigid (C.ImplType cP cQ), N.MetaTypeType)
  TermAst (ConjProp p q) -> do
    cP <- check p (N.MetaTypeType)
    cQ <- check q (N.MetaTypeType)
    pure (C.Rigid (C.ConjType cP cQ), N.MetaTypeType)
  TermAst (DisjProp p q) -> do
    cP <- check p (N.MetaTypeType)
    cQ <- check q (N.MetaTypeType)
    pure (C.Rigid (C.DisjType cP cQ), N.MetaTypeType)
  TermAst (ForallProp body) -> do
    inTy <- freshTypeUV
    outTy <- closureOf (C.MetaTypeType)
    cBody <- check body (N.MetaFunType Explicit inTy outTy)
    pure (C.Rigid (C.AllType cBody), N.MetaTypeType)
  TermAst (ExistsProp body) -> do
    inTy <- freshTypeUV
    outTy <- closureOf (C.MetaTypeType)
    cBody <- check body (N.MetaFunType Explicit inTy outTy)
    pure (C.Rigid (C.SomeType cBody), N.MetaTypeType)
  TermAst (EqualProp x y) -> do
    ty <- freshTypeUV
    cX <- check x ty
    cY <- check y ty
    pure (C.Rigid (C.PropIdType cX cY), N.MetaTypeType)
  TermAst Bool -> pure (C.Rigid C.TwoType, N.ObjTypeType)
  TermAst BTrue -> pure (C.Rigid C.TwoIntro0, N.Rigid N.TwoType)
  TermAst BFalse -> pure (C.Rigid C.TwoIntro1, N.Rigid N.TwoType)
  TermAst (Equal term1 term2) -> do
    cTerm1 <- freshTypeUV >>= check term1
    cTerm2 <- freshTypeUV >>= check term2
    pure (C.Rigid (C.ObjIdType cTerm1 cTerm2), N.ObjTypeType)
  TermAst Refl -> do
    term <- freshTypeUV
    cTerm <- readback term
    pure (C.Rigid (C.ObjIdIntro cTerm), N.Rigid (N.ObjIdType term term))
  TermAst (Sig tys) -> do
    cTys <- go tys
    pure (C.RecType cTys, N.ObjTypeType)
    where
      go :: Elab sig m => Seq (NameAst, TermAst) -> m (Seq (Field, C.Term))
      go Empty = pure Empty
      go ((NameAst name, ty) :<| tys) = do
        cTy <- check ty (N.ObjTypeType)
        vTy <- eval cTy
        cTys <- bindLocal name vTy (go tys)
        pure ((nameToField name, cTy) <| cTys)
  TermAst (Struct fds) -> do
    (cFds, cTys) <- unzip <$> go fds
    pure (C.RecIntro cFds, N.RecType cTys)
    where
      go ::
        Elab sig m =>
        Seq (NameAst, TermAst) ->
        m (Seq ((Field, C.Term), (Field, N.Closure)))
      go Empty = pure Empty
      go ((NameAst name, fd) :<| fds) = do
        ty <- freshTypeUV
        cFd <- check fd ty
        cFds <- bindLocal name ty (go fds)
        tyClo <- readback ty >>= closureOf
        pure (((nameToField name, cFd), (nameToField name, tyClo)) <| cFds)
  TermAst (Select str (NameAst name)) -> do
    (cStr, strTy) <- infer str
    strTy' <- unfold strTy
    case strTy' of
      N.RecType fdTys -> do
        fdTy <- go cStr Empty fdTys
        pure (C.RecElim cStr (nameToField name), fdTy)
      _ -> do
        cStrTy <- readback strTy
        errorTerm (ExpectedRecordType cStrTy)
    where
      go ::
        Elab sig m =>
        C.Term ->
        Seq N.Term ->
        Seq (Field, N.Closure) ->
        m N.Term
      go _ _ Empty = do
        report (MissingField name)
        pure (N.Rigid N.ElabError)
      go str defs ((fd, ty) :<| tys) =
        if fd == nameToField name then
          -- FIXME: `Elaboration.Effect` version of `appClosureN`
          appClosureN ty defs
        else do
          vTy <- appClosureN ty defs >>= unfold
          def <- case vTy of
            N.Rigid (N.SingType _ term) -> pure term
            _ -> eval (C.RecElim str fd)
          define def (go str (def <| defs) tys)
  TermAst (Patch sig defs) -> do
    cSig <- check sig (N.ObjTypeType)
    vSig <- eval cSig >>= unfold
    case vSig of
      N.RecType tys -> do
        cSig' <- C.RecType <$> go Empty Empty tys
        pure (cSig', N.ObjTypeType)
      _ -> errorTerm (ExpectedRecordType cSig)
    where
      go ::
        Elab sig m =>
        Seq N.Term ->
        Seq N.Term ->
        Seq (Field, N.Closure) ->
        m (Seq (Field, C.Term))
      go _ _ Empty = pure Empty
      go vDefs vRDefs ((fd, ty) :<| tys) = do
        vTy <- appClosureN ty vDefs
        case find (\(NameAst name, _) -> fd == nameToField name) defs of
          Just (NameAst name, def) -> do
            cDef <- check def vTy
            cTy <- appClosureN ty vRDefs >>= readback
            vDef <- eval cDef
            cDef' <- readback vDef
            l <- level
            cTys <-
              defineLocal -- FIXME? Wrap `vTy` and `vDef` in singleton forms
                name
                vTy
                vDef
                (go (vDef <| vDefs) (N.LocalVar l <| vRDefs) tys)
            pure ((fd, C.Rigid (C.SingType cTy cDef')) <| cTys)
          Nothing -> do
            l <- level
            cTy <- appClosureN ty vRDefs >>= readback
            cTys <- 
              bindLocal
                (fieldToName fd)
                vTy
                (go (N.LocalVar l <| vDefs) (N.LocalVar l <| vRDefs) tys)
            pure ((fd, cTy) <| cTys)
  TermAst ListTypeNil -> pure (C.Rigid C.ListTypeNil, N.ListTypeType)
  TermAst (ListTypeCons ty1 ty2) -> do
    cTy1 <- check ty1 N.MetaTypeType
    cTy2 <- check ty2 N.ListTypeType
    pure (C.Rigid (C.ListTypeCons cTy1 cTy2), N.ListTypeType)
  TermAst ListNil -> pure (C.Rigid C.ListIntroNil, N.Rigid N.ListTypeNil)
  TermAst (ListCons term1 term2) -> do
    ty1 <- freshTypeUV
    ty2 <- freshTypeUV
    cTerm1 <- check term1 ty1
    cTerm2 <- check term2 ty2
    pure
      ( C.Rigid (C.ListIntroCons cTerm1 cTerm2)
      , N.Rigid (N.ListTypeCons ty1 ty2))
  TermAst LCUniv -> pure (C.LowCTypeType, N.MetaTypeType)
  TermAst CIntType -> pure (C.Rigid C.CIntType, N.LowCTypeType)
  TermAst (CLValType ty) -> do
    cTy <- check ty N.LowCTypeType
    pure (C.Rigid (C.CLValType cTy), N.LowCTypeType)
  TermAst (CInt x) -> pure (C.Rigid (C.CIntIntro x), N.Rigid N.CIntType)
  TermAst (CPtrType ty) -> do
    cTy <- check ty N.LowCTypeType
    pure (C.Rigid (C.CPtrType cTy), N.LowCTypeType)
  TermAst CStmtType -> pure (C.Rigid C.CStmtType, N.MetaTypeType)
  TermAst CReturn -> pure (C.Rigid C.CStmtIntroRet, N.Rigid N.CStmtType)
  TermAst (CIf cond body1 body2) -> do
    cCond <- check cond (N.Rigid N.CIntType)
    cBody1 <- check body1 (N.Rigid N.CStmtType)
    cBody2 <- check body2 (N.Rigid N.CStmtType)
    pure (C.Rigid (C.CStmtIntroIf cCond cBody1 cBody2), N.Rigid N.CStmtType)
  TermAst (CWhile cond body) -> do
    cCond <- check cond (N.Rigid N.CIntType)
    cBody <- check body (N.Rigid N.CStmtType)
    pure (C.Rigid (C.CStmtIntroWhl cCond cBody), N.Rigid N.CStmtType)
  TermAst CBreak -> pure (C.Rigid C.CStmtIntroBrk, N.Rigid N.CStmtType)
  TermAst (CStructType tys) -> do
    cTys <- check tys N.ListTypeType
    pure (C.Rigid (C.CStructType cTys), N.LowCTypeType)
  TermAst (CStruct terms) -> do
    ty <- freshTypeUV
    cTerms <- check terms ty
    pure (C.Rigid (C.CStructIntro cTerms), N.Rigid (N.CStructType ty))
  TermAst (CApp lam args) -> do
    (cLam, lamTy) <- infer lam
    ty <- freshTypeUV
    unifyR (N.Rigid (N.CLValType ty)) lamTy
    argsTy <- go ty
    cArgs <- check args argsTy
    pure (C.Rigid (C.CStmtIntroCall cLam cArgs), N.Rigid N.CStmtType)
    where
      go :: Elab sig m => N.Term -> m N.Term
      go ty = do
        ty <- unfold ty
        case ty of
          N.MetaFunType Explicit inTy outTy -> do
            vOutTy <- evalClosure outTy
            ty' <- go vOutTy
            pure (N.Rigid (N.ListTypeCons inTy ty'))
          N.Rigid N.CStmtType -> pure (N.Rigid N.ListTypeNil)
  TermAst (CAdd term1 term2) -> do
    cTerm1 <- check term1 (N.Rigid N.CIntType)
    cTerm2 <- check term2 (N.Rigid N.CIntType)
    pure (C.Rigid (C.CIntElimAdd cTerm1 cTerm2), N.Rigid N.CIntType)
  TermAst (CSeq stmt1 stmt2) -> do
    cStmt1 <- check stmt1 (N.Rigid N.CStmtType)
    cStmt2 <- check stmt2 (N.Rigid N.CStmtType)
    pure (C.Rigid (C.CStmtIntroSeq cStmt1 cStmt2), N.Rigid N.CStmtType)
  TermAst (CDeclVar ty cont) -> do
    cTy <- check ty N.LowCTypeType
    vTy <- N.Rigid . N.CLValType <$> eval cTy
    clo <- closureOf (C.Rigid C.CStmtType)
    cCont <- check ty (N.MetaFunType Explicit vTy clo)
    pure (C.Rigid (C.CStmtIntroBind cTy cCont), N.Rigid N.CStmtType)
  TermAst (CAssign var term) -> do
    ty1 <- freshTypeUV
    ty2 <- freshTypeUV
    cVar <- check var (N.Rigid (N.CLValType ty1))
    cTerm <- check term ty2
    pure (C.Rigid (C.CStmtIntroSet cVar cTerm), N.Rigid N.CStmtType)
  TermAst (CEq term1 term2) -> do
    cTerm1 <- check term1 (N.Rigid N.CIntType)
    cTerm2 <- check term2 (N.Rigid N.CIntType)
    pure (C.Rigid (C.CIntElimEq cTerm1 cTerm2), N.Rigid N.CIntType)
  TermAst (CRef term) -> do
    ty <- freshTypeUV
    cTerm <- check term (N.Rigid (N.CLValType ty))
    pure (C.Rigid (C.CPtrIntro cTerm), N.Rigid (N.CPtrType ty))
  TermAst (CDerefLVal term) -> do
    ty <- freshTypeUV
    cTerm <- check term (N.Rigid (N.CPtrType ty))
    pure (C.Rigid (C.CPtrElimLVal cTerm), N.Rigid (N.CLValType ty))
  TermAst (CDerefRVal term) -> do
    ty <- freshTypeUV
    cTerm <- check term (N.Rigid (N.CPtrType ty))
    pure (C.Rigid (C.CPtrElimRVal cTerm), ty)
  TermAst (CCast ty term) -> do
    cTy <- check ty N.LowCTypeType
    vTy <- eval cTy
    ty' <- freshTypeUV
    cTerm <- check term ty'
    pure (C.Rigid (C.CCast cTy cTerm), vTy)
  TermAst (CLam lam) -> do
    (cLam, lamTy) <- noLocals (infer lam)
    pure (C.Rigid (C.CFunIntro cLam), N.Rigid (N.CFunType lamTy))
  TermAst (CLamType ty) -> do
    cTy <- check ty N.MetaTypeType -- TODO: Form check
    r <- eval cTy >>= formCheck
    if r then
      pure (C.Rigid (C.CFunType cTy), N.LowCTypeType)
    else
      pure (C.Rigid C.ElabError, N.LowCTypeType)
    where
      formCheck :: Elab sig m => N.Term -> m Bool
      formCheck ty = do
        ty <- unfold ty
        case ty of
          N.MetaFunType _ _ outTy -> do
            vOutTy <- evalClosure outTy
            formCheck vOutTy
          N.Rigid N.CStmtType -> pure True
          _ -> pure False
  TermAst (Declare name ty cont) -> do
    cTy <- check ty N.ObjTypeType
    vTy <- eval cTy
    cName <- check name (N.Rigid (N.NameType N.Obj vTy))
    contTy <- freshTypeUV
    cCont <- check cont contTy
    pure (C.Declare N.Obj cName cTy cCont, contTy)
  TermAst (Define name def cont) -> do
    ty <- freshTypeUV
    cName <- check name (N.Rigid (N.NameType N.Obj ty))
    cDef <- check def ty
    contTy <- freshTypeUV
    cCont <- check cont contTy
    pure (C.Define cName cDef cCont, contTy)
  TermAst (CDeclare name ty cont) -> do
    cTy <- check ty N.LowCTypeType
    vTy <- eval cTy
    cName <- check name (N.Rigid (N.NameType N.LowC vTy))
    contTy <- freshTypeUV
    cCont <- check cont contTy
    pure (C.Rigid (C.CDeclare cName cTy cCont), contTy)
  TermAst (CDefine name def cont) -> do
    ty <- freshTypeUV
    cName <- check name (N.Rigid (N.NameType N.LowC ty))
    cDef <- check def ty
    contTy <- freshTypeUV
    cCont <- check cont contTy
    pure (C.Rigid (C.CDefine cName cDef cCont), contTy)
  TermAst (NameType univ ty) -> do
    cTy <- check ty (N.Rigid (N.TypeType univ))
    pure (C.Rigid (C.NameType univ cTy), N.MetaTypeType)

checkMetaType :: Elab sig m => TermAst -> m (C.Term, N.Universe)
checkMetaType term =
  (,) <$> check term (N.MetaTypeType) <*> pure N.Meta

checkMetaType' :: Elab sig m => TermAst -> m C.Term
checkMetaType' ty = fst <$> checkMetaType ty

checkObjType :: Elab sig m => TermAst -> m (C.Term, N.Universe)
checkObjType term =
  (,) <$> check term (N.ObjTypeType) <*> pure N.Obj

checkObjType' :: Elab sig m => TermAst -> m C.Term
checkObjType' ty = fst <$> checkObjType ty

declsIds :: Seq DeclarationAst -> Seq Id
declsIds = concatMap go where
  go :: DeclarationAst -> Seq Id
  go (SourcePos decl _) = go decl
  go decl = singleton (unId decl)
