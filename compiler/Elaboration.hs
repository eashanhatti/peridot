{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
-- {-# OPTIONS_GHC -fdefer-type-errors #-}

module Elaboration where

import Data.List(foldl', find)
import qualified Data.Map as Map
import qualified Norm as N
import qualified Unification as U
import qualified Surface as S
import qualified Core as C
import Var
import Control.Monad.State(State, get, put, runState)
import Control.Monad(forM)
import Data.Foldable(foldlM)
import Control.Monad.Reader(runReader, Reader, ask, local)
import qualified Data.Set as Set
import Data.Set(singleton, Set)
import qualified Data.Map as Map
import Data.Map(Map, (!))
import Debug.Trace
import GHC.Stack
import Prelude hiding(Ordering)
-- import Debug.Pretty.Simple(pTraceShowId, pTrace)
import Data.Maybe(fromJust)
import Etc
import Elaboration.Error

data ElabState = ElabState
  { metas :: N.Metas
  , nextMeta :: Int
  , goalUniv :: N.Value
  , errors :: [Error]
  , locals :: N.Locals
  , ltypes :: Map S.Name (N.Value, Index)
  , level :: Level
  , binderInfos :: [C.BinderInfo]
  , nextName :: Int
  , reservedNames :: [S.Name]
  , globals :: Map S.GName C.Item
  , idsNames :: Map Id S.GName
  , nextId :: Int }
  deriving Show

clearState :: ElabState -> Set S.GName -> ElabState
clearState state changes = ElabState
  mempty
  0
  (N.gen N.TypeType1)
  []
  []
  mempty
  (Level 0)
  []
  0
  []
  (Map.filterWithKey (\name _ -> Set.notMember name changes) (globals state))
  (Map.filter (\name -> Set.notMember name changes) (idsNames state))
  (nextId state)

startingState = ElabState mempty 0 (N.gen N.TypeType1) [] [] mempty (Level 0) [] 0 [] mempty mempty 0

type Elab a = State ElabState a

data Item
  = TermDef S.Term S.Term
  | IndDef S.Term C.IndDefInfo
  | ProdDef S.Term [S.Term]
  | ConDef S.GName S.Term
  deriving Show

type Program = Map S.GName Item
-- Mapping from items to the items they depend on, and where the dependency occurs
type Graph = Map S.GName (Map S.GName (Set S.ItemPart))
type Cycles = [(S.GName, [S.GName])]
type Ordering = [Set S.GName]
type ChangedItems = Map S.GName S.ItemPart
-- Mapping from items to the items that depend on them, and where the dependency occurs
type ReverseDeps = Map S.GName (Map S.GName (Set S.ItemPart))

elabFresh :: HasCallStack => S.Item -> (C.Program, ElabState)
elabFresh item =
  let ((p, _), s) = runState (checkProgram (flatten [] item)) startingState
  in (p, s)

reverseDeps :: Graph -> ReverseDeps
reverseDeps graph = Map.mapWithKey (\name _ -> go name) graph where
  go :: S.GName -> Map S.GName (Set S.ItemPart)
  go name = fmap (fromJust . Map.lookup name) $ Map.filter (Map.member name) graph

elab :: HasCallStack => S.Item -> ElabState -> C.Program -> ChangedItems -> ReverseDeps -> (C.Program, Graph, ElabState)
elab item oldState oldProgram changes deps =
  let
    flatItems = flatten [] item
    -- changed part -> dependencies -> changed items
    go :: S.ItemPart -> Map S.GName (Set S.ItemPart) -> Program
    go part items = Map.foldl' Map.union mempty $ (flip Map.mapWithKey) items \name ps ->
      let
        m = case (part, ps) of
          (S.Dec, Set.member S.Dec -> True)         -> go S.Dec (deps ! name)
          (S.Dec, (== Set.singleton S.Def) -> True) -> mempty
          (S.Def, Set.member S.Dec -> True)         -> go S.Dec (deps ! name)
          (S.Def, (== Set.singleton S.Def) -> True) -> go S.Def (deps ! name)
      in Map.singleton name (flatItems ! name) `Map.union` m

    pairs = Map.elems $ Map.mapWithKey (\name part -> (part, deps ! name)) changes
    program = mconcat (map (uncurry go) pairs) `Map.union` Map.fromList (map (\name -> (name, flatItems ! name)) (Map.keys changes))
    
    -- old program -> new program -> combined program
    combinePrograms :: C.Program -> C.Program -> C.Program
    combinePrograms (C.Program oldProg) (C.Program newProg) = C.Program $ map go oldProg where
      go :: C.Item -> C.Item
      go oldItem@(C.itemId -> nid) = case find (\(C.itemId -> nid') -> nid == nid') newProg of
        Just newItem -> newItem
        Nothing -> oldItem

    ((cProgram, graph), state) = runState (checkProgram program) oldState
  in (combinePrograms oldProgram cProgram, graph, state)

flatten :: [String] -> S.Item -> Program
flatten nameAcc item = case item of
  S.EditorFocusDef item _ -> flatten nameAcc item
  S.EditorBlankDef -> mempty
  S.NamespaceDef name items -> foldl' Map.union mempty (map (flatten ((S.unName name):nameAcc)) items)
  S.TermDef name dec def -> Map.singleton (S.GName $ (S.unName name):nameAcc) (TermDef dec def)
  S.ProdDef name dec fields -> Map.singleton (S.GName $ (S.unName name):nameAcc) (ProdDef dec fields)
  S.IndDef name dec cs ->
    Map.union
      (Map.singleton (S.GName $ (S.unName name):nameAcc) (IndDef dec (C.IndDefInfo $ map (S.unName . fst) cs)))
      (Map.fromList $ map
        (\(cn, ct) ->
          let gname = S.unName cn : S.unName name : nameAcc
          in (S.GName gname, ConDef (S.GName $ tail gname) ct))
        cs)

dependencies :: [(S.GName, Item)] -> Graph
dependencies items = case items of
  (name, item):items ->
    let
      ds = Map.singleton name $ case item of
        TermDef dec def -> searchTy dec `combine` search def
        IndDef dec _ -> searchTy dec
        ProdDef dec fields -> searchTy dec `combine` runReader (searchTerms fields) S.Dec
        ConDef tyName ty -> searchTy ty
    in ds `Map.union` dependencies items
  [] -> mempty
  where
    search term = runReader (search' term) S.Def
    searchTy term = runReader (search' term) S.Dec

    search' :: S.Term -> Reader S.ItemPart (Map S.GName (Set S.ItemPart))
    search' term = case term of
      S.EditorFocus term _ -> search' term
      S.Var _ -> pure mempty
      S.GVar (S.GName name) -> do
        p <- ask
        pure $ Map.singleton (S.GName $ name) (Set.singleton p)
      S.Lam _ body -> search' body
      S.App lam args -> combine <$> search' lam <*> searchTerms args where
      S.Ann _ ty -> local (const S.Dec) $ search' ty
      S.Pi _ inTy outTy -> combine <$> search' inTy <*> search' outTy
      S.Let _ def defTy body -> combine <$> search' def <*> (combine <$> (local (const S.Dec) $ search' defTy) <*> search' body)
      S.U0 -> pure mempty
      S.U1 -> pure mempty
      S.Code term -> search' term
      S.Quote term -> search' term
      S.Splice term -> search' term
      S.MkProd ty fields -> combine <$> search' ty <*> searchTerms fields
      S.Hole -> pure mempty
      S.EditorBlank -> pure mempty
    searchTerms :: [S.Term] -> Reader S.ItemPart (Map S.GName (Set S.ItemPart))
    searchTerms as = case as of
      [] -> pure mempty
      a:as -> do
        names <- search' a
        names' <- searchTerms as
        pure $ combine names names'
    combine :: Map S.GName (Set S.ItemPart) -> Map S.GName (Set S.ItemPart) -> Map S.GName (Set S.ItemPart)
    combine = Map.unionWith Set.union

cycles :: Graph -> Cycles
cycles graph = []

ordering :: Graph-> Either Cycles Ordering
ordering graph = case cycles graph of
  [] -> Right $ loop (Map.map (Map.keysSet . Map.filter (Set.member S.Dec)) graph) mempty
  cs -> Left cs
  where
    loop :: Map S.GName (Set S.GName) -> Set S.GName -> Ordering
    loop graph available = -- traceShow available $
      if available == Map.keysSet graph then
        []
      else
        let nowAvailable = Map.keysSet $ Map.filter (\ds -> ds `Set.isSubsetOf` available) graph
        in (nowAvailable `Set.difference` available):(loop graph (nowAvailable `Set.union` available))

checkProgram :: HasCallStack => Program -> Elab (C.Program, Graph)
checkProgram program =
  let deps = dependencies (Map.toList program)
  in case ordering deps of
    Right ord -> do
      loopDeclare program ord
      program <- loopDefine program ord
      pure (C.Program program, deps)
    Left cs -> error "TODO: Cycle detection"
  where
    loopDeclare :: HasCallStack => Program -> Ordering -> Elab ()
    loopDeclare program ord = case ord of
      [] -> pure ()
      names:ord -> do
        declareGlobals (Set.toList names) program
        loopDeclare program ord
    loopDefine :: HasCallStack => Program -> Ordering -> Elab [C.Item]
    loopDefine program ord = case ord of
      [] -> pure []
      names:ord -> do
        cItems <- defineGlobals (Set.toList names) program
        cItems' <- loopDefine program ord
        pure $ cItems ++ cItems'
    declareGlobals :: HasCallStack => [S.GName] -> Program -> Elab ()
    declareGlobals names program = case names of
      [] -> pure ()
      name:names -> do
        let item = fromJust $ Map.lookup name program
        ty <- case item of
          TermDef ty _ -> do
            meta <- freshUnivMeta >>= eval
            putGoalUniv meta
            check ty meta >>= eval
          ProdDef ty _ -> check ty (N.gen N.TypeType1) >>= eval
          IndDef ty _ -> check ty (N.gen N.TypeType1) >>= eval
          ConDef _ ty -> check ty (N.gen N.TypeType1) >>= eval
        declareGlobal name ty
        declareGlobals names program
    declareGlobal :: HasCallStack => S.GName -> N.Value -> Elab ()
    declareGlobal name ty = do
      nid <- freshId
      cTy <- readback ty
      state <- get
      put $ state { globals = Map.insert name (C.ElabBlankItem nid cTy) (globals state) }
    defineGlobals :: HasCallStack => [S.GName] -> Program -> Elab [C.Item]
    defineGlobals names program = case names of
      [] -> pure []
      name:names -> do
        let item = fromJust $ Map.lookup name program
        (cItem, itemTy) <- checkItem item name
        defineGlobal name cItem itemTy
        cItems <- defineGlobals names program
        pure $ cItem:cItems
    defineGlobal :: HasCallStack => S.GName -> C.Item -> N.Value -> Elab ()
    defineGlobal name item ty = do
      state <- get
      put $ state
        { globals = Map.insert name item (globals state)
        , idsNames = Map.insert (C.itemId item) name (idsNames state) }
    checkItem :: HasCallStack => Item -> S.GName -> Elab (C.Item, N.Value)
    checkItem item name = do
      gs <- globals <$> get
      let nid = case Map.lookup name gs of Just (C.ElabBlankItem nid _) -> nid
      meta <- freshUnivMeta >>= eval
      case item of
        TermDef dec def -> do
          putGoalUniv meta
          cDec <- check dec meta
          vDec <- eval cDec
          cDef <- check def vDec
          pure (C.TermDef nid cDef cDec, vDec)
        IndDef dec info -> do
          cDec <- check dec (N.gen N.TypeType1)
          pure (C.IndDef nid cDec info, N.gen N.TypeType1)
        ProdDef dec fields -> do
          cDec' <- check dec (N.gen N.TypeType1)
          err <- bindParams dec
          cFields <- mapM ((flip check) (N.gen N.TypeType0)) fields
          let
            cDec = case err of
              Just err -> C.withErrs [err] cDec'
              Nothing -> cDec'
          pure (C.ProdDef nid cDec cFields, N.gen N.TypeType0)
          where
            bindParams :: S.Term -> Elab (Maybe Error)
            bindParams term = case term of
              S.Pi name inTy outTy -> do
                vInTy <- check inTy (N.gen N.TypeType1) >>= eval
                bind name vInTy
                bindParams outTy
              S.U0 -> pure Nothing
              _ -> do
                err <- putError MalformedProdDec
                pure $ Just err
        ConDef name ty -> do
          cTy <- check ty (N.gen $ N.TypeType1)
          vTy <- eval cTy
          pure (C.ConDef nid cTy, vTy)
    validateCon :: S.GName -> C.Term -> Elab ()
    validateCon name ty = pure ()

check :: HasCallStack => S.Term -> N.Value -> Elab C.Term
check term goal = do
  -- let !() = trace ("Goal = " ++ show goal) ()
  goal <- force goal
  -- let !() = trace ("Term = " ++ show term) ()
  -- let !() = trace ("FGoal = " ++ show goal) ()
  cGoal <- readback goal
  univ <- getGoalUniv
  -- let !() = trace ("CGoal = " ++ show cGoal) ()
  scope case (term, N.unVal goal) of
    (S.EditorFocus term' side, _) -> do
      C.Term (C.Info _ errs) cTerm' <- check term' goal
      pure $ C.Term (C.Info (Just side) errs) cTerm'
    (S.Ann term' ty, _) -> do
      cTy <- check ty univ
      vTy <- eval cTy
      errs <- unify goal vTy
      C.withErrs errs <$> check term' vTy
    (S.Lam names body, _) -> go names goal >>= \case
      Right cTerm -> pure cTerm
      Left err -> pure $ C.withErrsGen [err] $ C.ElabError term
      where
        go :: [S.Name] -> N.Value -> Elab (Either Error C.Term)
        go ns g = case (ns, g) of
          ([], _) -> error "Empty"
          ([n], ty@(N.unVal -> N.FunType inTy outTy _)) -> do
            cTy <- readback ty
            vOutTy <- appClosure outTy inTy
            bind n inTy
            cBody <- check body vOutTy
            pure $ Right $ C.gen $ C.FunIntro cBody cTy (C.FunIntroInfo 1 n)
          (n:ns, ty@(N.unVal -> N.FunType inTy outTy _)) -> do
            cTy <- readback ty
            vOutTy <- appClosure outTy inTy
            bind n inTy
            go ns vOutTy >>= \case
              Right cBody -> pure $ Right $ C.gen $ C.FunIntro cBody cTy (C.FunIntroInfo (fromIntegral $ length ns + 1) n)
              Left err -> pure $ Left err
          (_, _) -> do
            err <- putError TooManyParams
            pure $ Left err
    (S.Let name def defTy body, _) -> do
      reserve [name]
      vDefTy <- check defTy univ >>= eval
      cDef <- check def vDefTy
      vDef <- eval cDef
      defineReserved name vDef vDefTy
      cBody <- check body goal
      pure $ C.gen $ C.Letrec [cDef] cBody (C.LetrecInfo name)
    (S.Hole, _) -> freshMeta cGoal
    (S.Quote inner, N.QuoteType ty) -> do
      errs <- unify univ (N.gen $ N.TypeType1)
      putGoalUniv (N.gen $ N.TypeType0)
      cInner <- check inner ty
      cTy <- readback ty
      pure $ C.withErrsGen errs $ C.QuoteIntro cInner cTy
    (S.MkProd ty fields, N.ProdType tid _) -> do
      cTy <- check ty (N.gen N.TypeType1)
      vTy <- eval cTy
      errs <- unify goal vTy
      C.withErrs errs <$> (globalDefFromId tid >>= \case
        Just (C.ProdDef _ _ fieldTypes) ->
          if length fieldTypes == length fields then do
            vFieldTypes <- mapM eval fieldTypes
            cFields <- mapM (\(f, t) -> check f t) (zip fields vFieldTypes)
            pure $ C.gen $ C.ProdIntro cTy cFields
          else do
            err <- putError MismatchedFieldNumber
            pure $ C.withErrsGen [err] $ C.ElabError term)
    (_, N.QuoteType ty) | N.unVal univ /= N.TypeType1 -> do
      putGoalUniv (N.gen $ N.TypeType0)
      (cTerm, termTy) <- infer term
      cTermTy <- readback termTy
      pure $ C.gen $ C.QuoteIntro cTerm cTermTy
    (_, _) -> do
      (cTerm, ty) <- infer term
      errs <- unify goal ty
      pure $ C.withErrs errs cTerm

infer :: HasCallStack => S.Term -> Elab (C.Term, N.Value)
infer term = getGoalUniv >>= \univ -> scope case term of
  S.EditorFocus term' side -> do
    (C.Term (C.Info _ errs) cTerm', ty) <- infer term'
    pure $ (C.Term (C.Info (Just side) errs) cTerm', ty)
  S.Ann term' ty -> do
    vTy <- check ty univ >>= eval
    cTerm' <- check term' vTy
    pure (cTerm', vTy)
  S.Var name -> do
    entry <- localType name
    case entry of
      Just (ty, ix) -> do
        cTy <- readback ty
        pure (C.gen $ C.Var ix cTy (C.VarInfo $ S.unName name), ty)
      Nothing -> do
        err <- putError $ UnboundLocal name
        pure (C.withErrsGen [err] $ C.ElabError term, N.gen $ N.ElabBlank)
  S.GVar name -> do
    entry <- globalDef name
    case entry of
      Just def -> do
        ty <- case def of
          C.TermDef _ _ ty -> pure ty 
          C.IndDef _ ty _ -> pure ty
          C.ConDef _ ty -> pure ty
          C.ProdDef _ ty _ -> pure ty
          C.ElabBlankItem nid ty -> pure ty
        vTy <- eval ty
        pure (C.gen $ C.GVar (C.itemId def) ty (C.GVarInfo $ S.unGName name), vTy)
      Nothing -> do
        err <- putError $ UnboundGlobal name
        pure (C.withErrsGen [err] $ C.ElabError term, N.gen $ N.ElabBlank)
  S.Lam names body -> go names where
    go :: [S.Name] -> Elab (C.Term, N.Value)
    go ns = case ns of
      [n] -> do
        cMeta <- readback univ >>= freshMeta
        vMeta <- eval cMeta
        bind n vMeta
        (cBody, vBodyTy) <- infer body
        closure <- closeValue vBodyTy
        cBodyTy <- readback vBodyTy
        let ty = N.gen $ N.FunType vMeta closure (C.FunTypeInfo n)
        pure (C.gen $ C.FunIntro cBody (C.gen $ C.FunType cMeta cBodyTy (C.FunTypeInfo n)) (C.FunIntroInfo 1 n), ty)
      n:ns -> do
        cMeta <- readback univ >>= freshMeta
        vMeta <- eval cMeta
        bind n vMeta
        (cBody, vBodyTy) <- go ns
        closure <- closeValue vBodyTy
        cBodyTy <- readback vBodyTy
        let ty = N.gen $ N.FunType vMeta closure (C.FunTypeInfo n)
        pure (C.gen $ C.FunIntro cBody (C.gen $ C.FunType cMeta cBodyTy (C.FunTypeInfo n)) (C.FunIntroInfo (fromIntegral $ length ns + 1) n), ty)
  S.App lam args -> do
    (cLam, lamTy) <- infer lam
    (cArgs, outTy) <- go cLam args lamTy
    pure (mkElims (reverse cArgs) cLam, outTy)
    where
      mkElims :: [(C.Term, [Error])] -> C.Term -> C.Term
      mkElims cArgs cLam = case cArgs of
        [] -> error "Empty2"
        [(a, errs)] -> C.withErrsGen errs $ C.FunElim cLam a (C.FunElimInfo 1)
        (a, errs):cArgs -> C.withErrsGen errs $ C.FunElim (mkElims cArgs cLam) a (C.FunElimInfo $ fromIntegral $ length cArgs + 1)
      go :: C.Term -> [S.Term] -> N.Value -> Elab ([(C.Term, [Error])], N.Value)
      go cLam as lty = case (as, N.unVal lty) of
        ([], _) -> error "Empty"
        ([a], N.FunType inTy outTy _) -> do
          cArg <- check a (traceShowId inTy)
          vArg <- eval cArg
          outTy <- evalClosure outTy vArg
          pure ([(cArg, [])], outTy)
        ([a], _) -> do
          inTy <- readback univ >>= freshMeta
          vInTy <- eval inTy
          cArg <- check a vInTy
          name <- freshName "p"
          (outTy, vOutTy) <- scope do
            bind name vInTy
            outTy <- readback univ >>= freshMeta
            vOutTy <- eval outTy
            pure (outTy, vOutTy)
          outTyClo <- closeTerm outTy
          errs <- unify lty (N.gen $ N.FunType vInTy outTyClo (C.FunTypeInfo $ S.Name "_"))
          pure ([(cArg, errs)], vOutTy)
        (a:as, N.FunType inTy outTy _) -> do
          cArg <- check a (traceShowId inTy)
          vArg <- eval cArg
          outTy <- evalClosure outTy vArg
          (cArgs, outTyInner) <- go cLam as outTy
          pure ((cArg, []):cArgs, outTyInner)
        (a:as, _) -> do
          inTy <- readback univ >>= freshMeta
          vInTy <- eval inTy
          cArg <- check a vInTy
          name <- freshName "p"
          (outTy, vOutTy) <- scope do
            bind name vInTy
            outTy <- readback univ >>= freshMeta
            vOutTy <- eval outTy
            pure (outTy, vOutTy)
          outTyClo <- closeTerm outTy
          errs <- unify lty (N.gen $ N.FunType vInTy outTyClo (C.FunTypeInfo $ S.Name "_"))
          (cArgs, outTyInner) <- go cLam as vOutTy
          pure ((cArg, errs):cArgs, outTyInner)
  S.U0 -> do
    errs <- unify univ (N.gen $ N.TypeType1)
    pure (C.withErrsGen errs $ C.TypeType0, N.gen $ N.TypeType1)
  S.U1 -> do
    errs <- unify univ (N.gen $ N.TypeType1)
    pure (C.withErrsGen errs $ C.TypeType1, N.gen $ N.TypeType1)
  S.Pi name inTy outTy -> do
    cInTy <- check inTy univ
    vInTy <- eval cInTy
    bind name vInTy
    cOutTy <- check outTy univ
    pure (C.gen $ C.FunType cInTy cOutTy (C.FunTypeInfo name), univ)
  S.Code ty -> do
    errs <- unify univ (N.gen $ N.TypeType1)
    putGoalUniv (N.gen $ N.TypeType0)
    cTy <- check ty (N.gen $ N.TypeType0)
    pure (C.withErrsGen errs $ C.QuoteType cTy, N.gen $ N.TypeType1)
  S.Quote inner -> do
    errs <- unify univ (N.gen $ N.TypeType1)
    putGoalUniv (N.gen $ N.TypeType0)
    (cInner, innerTy) <- infer inner
    cInnerTy <- readback innerTy
    pure (C.withErrsGen errs $ C.QuoteIntro cInner cInnerTy, N.gen $ N.QuoteType innerTy)
  S.Splice quote -> do
    errs <- unify univ (N.gen $ N.TypeType0)
    putGoalUniv (N.gen $ N.TypeType1)
    (cQuote, quoteTy) <- infer quote
    quoteInnerTy <- case N.unVal quoteTy of
      N.QuoteType ty -> pure ty
      _ -> freshMeta (C.gen $ C.TypeType0) >>= eval
    pure (C.withErrsGen errs $ C.QuoteElim cQuote, quoteInnerTy)
  S.MkProd ty fields -> do
    cTy <- check ty (N.gen $ N.TypeType1)
    vTy <- eval cTy
    case N.unVal vTy of
      N.ProdType tid _ -> globalDefFromId tid >>= \case
        Just (C.ProdDef _ _ fieldTypes) ->
          if length fieldTypes == length fields then do
            vFieldTypes <- mapM eval fieldTypes
            cFields <- mapM (\(f, t) -> check f t) (zip fields vFieldTypes)
            pure (C.gen $ C.ProdIntro cTy cFields, vTy)
          else do
            err <- putError MismatchedFieldNumber
            pure (C.withErrsGen [err] $ C.ElabError term, N.gen N.ElabBlank)
      _ -> do
        err <- putError ExpectedProdType
        pure (C.withErrsGen [err] $ C.ElabError term, N.gen N.ElabBlank)
  S.Let name def defTy body -> do
    reserve [name]
    vDefTy <- check defTy univ >>= eval
    cDef <- check def vDefTy
    vDef <- eval cDef
    defineReserved name vDef vDefTy
    (cBody, vBodyTy) <- infer body
    pure (C.gen $ C.Letrec [cDef] cBody (C.LetrecInfo name), vBodyTy)
  S.Hole -> inferHole univ
  S.EditorBlank -> inferHole univ
  _ -> error $ "`infer`: " ++ show term
  where
    inferHole univ = do
      cTypeMeta <- readback univ >>= freshMeta
      vTypeMeta <- eval cTypeMeta
      cTermMeta <- freshMeta cTypeMeta
      pure (cTermMeta, vTypeMeta)

gnameMapToIdMap :: Map.Map S.GName C.Item -> N.Globals
gnameMapToIdMap globals = Map.fromList $ map (\(_, g) -> (C.itemId g, g)) (Map.toList globals)

runNorm :: HasCallStack => N.Norm a -> Elab a
runNorm act = do
  state <- get
  pure $ runReader act (level state, metas state, locals state, gnameMapToIdMap (globals state))

force :: N.Value -> Elab N.Value
force val = do
  state <- get
  runNorm $ N.force val

-- FIXME: better name
scope :: Elab a -> Elab a
scope act = do
  state <- get
  let (a, s) = runState act state
  put $ state { metas = metas s, errors = errors s, nextMeta = nextMeta s, nextName = nextName s, nextId = nextId s }
  pure a

reserve :: [S.Name] -> Elab ()
reserve names = do
  state <- get
  if reservedNames state == [] then pure () else error "`reserve`: `reservedNames` must be empty"
  put $ state
    { level = Level $ unLevel (level state) + (length names)
    , reservedNames = names }

defineReserved :: S.Name -> N.Value -> N.Value -> Elab ()
defineReserved name def ty = do
  state <- get
  if reservedNames state !! 0 == name then pure () else error "`defineReserved`: `name` must be first in `reservedNames`"
  put $ state
    { locals = def:(locals state)
    , ltypes = Map.insert name (ty, Index 0) $ Map.map (\(ty, ix) -> (ty, Index $ unIndex ix + 1)) (ltypes state)
    , binderInfos = C.Concrete:(binderInfos state)
    , reservedNames = tail (reservedNames state) }

bind :: S.Name -> N.Value -> Elab ()
bind name ty = do
  state <- get
  put $ state
    { locals = (N.gen $ N.StuckRigidVar ty (level state) [] (C.VarInfo $ S.unName name)):(locals state)
    , ltypes = Map.insert name (ty, Index 0) $ Map.map (\(ty, ix) -> (ty, Index $ unIndex ix + 1)) (ltypes state)
    , level = Level $ unLevel (level state) + 1
    , binderInfos = C.Abstract:(binderInfos state) }

define :: S.Name -> N.Value -> N.Value -> Elab ()
define name def ty = do
  state <- get
  put $ state
    { locals = def:(locals state)
    , ltypes = Map.insert name (ty, Index 0) $ Map.map (\(ty, ix) -> (ty, Index $ unIndex ix + 1)) (ltypes state)
    , level = Level $ unLevel (level state) + 1
    , binderInfos = C.Concrete:(binderInfos state) }

localType :: S.Name -> Elab (Maybe (N.Value, Index))
localType name = do
  state <- get
  pure $ Map.lookup name (ltypes state)

globalType :: Id -> Elab (Maybe C.Term)
globalType nid = do
  state <- get
  name <- idName nid
  pure $ fmap
    (\case
      C.IndDef _ ty _ -> ty
      C.ConDef _ ty -> ty)
    (Map.lookup name (globals state))

idName :: Id -> Elab S.GName
idName nid = do
  state <- get
  pure $ fromJust $ Map.lookup nid (idsNames state)

globalId :: S.GName -> Elab (Maybe Id)
globalId name = do
  state <- get
  pure $ fmap C.itemId (Map.lookup name (globals state))

globalDefFromId :: Id -> Elab (Maybe C.Item)
globalDefFromId nid = do
  state <- get
  let name = fromJust $ Map.lookup nid (idsNames state)
  def <- globalDef name
  pure def

globalDef :: S.GName -> Elab (Maybe C.Item)
globalDef name = do
  state <- get
  pure $ Map.lookup name (globals state)

appClosure :: HasCallStack => N.Closure -> N.Value -> Elab N.Value
appClosure closure ty = do
  state <- get
  runNorm $ N.appClosure closure (N.gen $ N.StuckRigidVar ty (level state) [] undefined)

-- FIXME: better name
evalClosure :: N.Closure -> N.Value -> Elab N.Value
evalClosure closure def = do
  state <- get
  runNorm $ N.appClosure closure def

closeValue :: N.Value -> Elab N.Closure
closeValue value = do
  state <- get
  term <- readback value
  pure $ N.Closure (locals state) term

closeTerm :: C.Term -> Elab N.Closure
closeTerm term = do
  state <- get
  pure $ N.Closure (locals state) term

readback :: HasCallStack => N.Value -> Elab C.Term
readback val = do
  state <- get
  runNorm $ N.readback val

eval :: HasCallStack => C.Term -> Elab N.Value
eval term = do
  state <- get
  runNorm $ N.eval term

freshMeta :: C.Term -> Elab C.Term
freshMeta ty = do
  state <- get
  let meta = C.gen $ C.InsertedMeta (binderInfos state) (Global $ nextMeta state) (Just ty)
  put $ state
    { metas = Map.insert (Global $ nextMeta state) N.Unsolved (metas state)
    , nextMeta = (nextMeta state) + 1 }
  pure meta

freshUnivMeta :: Elab C.Term
freshUnivMeta = do
  state <- get
  let meta = C.gen $ C.InsertedMeta (binderInfos state) (Global $ nextMeta state) Nothing
  put $ state
    { metas = Map.insert (Global $ nextMeta state) N.Unsolved (metas state)
    , nextMeta = (nextMeta state) + 1 }
  pure meta 

unify :: HasCallStack => N.Value -> N.Value -> Elab [Error]
unify val val' = do
  state <- get
  let ((), (newMetas, newErrors, _)) = U.runUnify (U.unify (level state) val val') (metas state, [], gnameMapToIdMap (globals state))
  errs <- case newErrors of
    [] -> do put $ state { metas = newMetas }; pure []
    _ -> forM (map UnifyError newErrors) putError
  pure errs

putError :: InnerError -> Elab Error
putError err = do
  state <- get
  let fullError = Error (locals state) (globals state) (level state) err
  put $ state { errors = fullError:(errors state) }
  pure fullError

freshName :: String -> Elab S.Name
freshName base = do
  state <- get
  let n = nextName state
  put $ state { nextName = nextName state + 1 }
  pure $ S.Name (base ++ show n)

putGoalUniv :: N.Value -> Elab ()
putGoalUniv univ = do
  state <- get
  put $ state { goalUniv = univ }

getGoalUniv :: Elab N.Value
getGoalUniv = do
  state <- get
  pure $ goalUniv state

typeof :: N.Value -> Elab N.Value
typeof val = do
  state <- get
  pure $ U.getVty (metas state) (level state) val

typeofC :: C.Term -> Elab C.Term
typeofC term = do
  state <- get
  U.getTty (metas state) (level state) <$> eval term

freshId :: Elab Id
freshId = do
  state <- get
  let nid = nextId state
  put $ state { nextId = nid + 1 }
  pure $ Id nid