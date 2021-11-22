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
import Control.Monad(forM_)
import Data.Foldable(foldlM)
import Control.Monad.Reader(runReader, Reader, ask, local)
import Debug.Trace
import qualified Data.Set as Set
import Data.Set(singleton, Set)
import qualified Data.Map as Map
import Data.Map(Map, (!))
import Debug.Trace
import GHC.Stack
import Prelude hiding(Ordering)
import Debug.Pretty.Simple(pTraceShowId, pTrace)
import Data.Maybe(fromJust)

data InnerError
  = UnboundLocal S.Name
  | UnboundGlobal S.GName
  | UnifyError U.Error
  | TooManyParams
  | MalformedProdDec
  | ExpectedProdType
  deriving Show

data Error = Error N.Locals (Map S.GName C.Item) Level InnerError

instance Show Error where
  show (Error ls gs lv e) = "Error\n" ++ show e ++ "\n" ++ indent "  " stringLocals ++ "\n" ++ indent "  " ("----\n" ++ stringGlobals)
    where
      indent :: String -> String -> String
      indent i s = unlines $ map (i++) (lines s)

      stringLocals = concat $ map (\l -> show l ++ "\n") ls
      stringGlobals = concat $ map (\(n, g) -> show n ++ " = " ++ show g ++ "\n") (Map.toList gs)      

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
  N.TypeType1
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

data OldElabState = OldElabState

type Elab a = State ElabState a

data Item
  = TermDef S.Term S.Term
  | IndDef S.Term
  | ProdDef S.Term [S.Term]
  | ConDef S.GName S.Term
  deriving Show

type Program = Map S.GName Item
type Graph = Map S.GName (Set S.GName)
type Cycles = [(S.GName, [S.GName])]
type Ordering = [Set S.GName]
data ItemPart = Dec | Def
  deriving (Eq, Ord)
type ChangedItems = Map S.GName ItemPart
type ReverseDeps = Map S.GName [(S.GName, Set ItemPart)]

elab :: HasCallStack => S.Item -> ElabState -> C.Program -> ChangedItems -> ReverseDeps -> (C.Program, ElabState)
elab item oldState oldProgram changes deps =
  let 
    flatItems = flatten [] item
    -- changed part -> dependencies -> changed items
    go :: ItemPart -> [(S.GName, Set ItemPart)] -> Program
    go part items = foldl' Map.union mempty $ (flip map) items \(name, ps) ->
      let
        m = case (part, ps) of
          (Dec, Set.member Dec -> True)         -> go Dec (deps ! name)
          (Dec, (== Set.singleton Def) -> True) -> mempty
          (Def, Set.member Dec -> True)         -> go Dec (deps ! name)
          (Def, (== Set.singleton Def) -> True) -> go Def (deps ! name)
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

    (cProgram, state) = runState (checkProgram program) oldState
  in (combinePrograms oldProgram cProgram, state)

flatten :: [String] -> S.Item -> Program
flatten nameAcc item = case item of
  S.NamespaceDef name items -> foldl' Map.union mempty (map (flatten ((S.unName name):nameAcc)) items)
  S.TermDef name dec def -> Map.singleton (S.GName $ (S.unName name):nameAcc) (TermDef dec def)
  S.ProdDef name dec fields -> Map.singleton (S.GName $ (S.unName name):nameAcc) (ProdDef dec fields)
  S.IndDef name dec cs ->
    Map.union
      (Map.singleton (S.GName $ (S.unName name):nameAcc) (IndDef dec))
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
        TermDef dec def -> searchTy dec `Set.union` search def
        IndDef dec -> searchTy dec
        ProdDef dec fields -> searchTy dec `Set.union` runReader (searchTerms fields) True
        ConDef name ty -> searchTy ty `Set.union` singleton name
    in ds `Map.union` dependencies items
  [] -> mempty
  where
    search term = runReader (search' term) False
    searchTy term = runReader (search' term) True

    search' :: S.Term -> Reader Bool (Set S.GName)
    search' term = case term of
      S.Var _ -> pure mempty
      S.GVar (S.GName name) -> ask >>= \b -> pure $ if b then singleton (S.GName $ name) else mempty
      S.Lam _ body -> search' body
      S.App lam args -> Set.union <$> search' lam <*> searchTerms args where
      S.Ann _ ty -> local (const True) $ search' ty
      S.Pi _ inTy outTy -> Set.union <$> search' inTy <*> search' outTy
      S.Let _ def defTy body -> Set.union <$> search' def <*> (Set.union <$> (local (const True) $ search' defTy) <*> search' body)
      S.U0 -> pure mempty
      S.U1 -> pure mempty
      S.Code term -> search' term
      S.Quote term -> search' term
      S.Splice term -> search' term
      S.MkProd ty fields -> Set.union <$> search' ty <*> searchTerms fields
      S.Hole -> pure mempty
    searchTerms :: [S.Term] -> Reader Bool (Set S.GName)
    searchTerms as = case as of
      [a] -> search' a
      a:as -> do
        names <- search' a
        names' <- searchTerms as
        pure $ Set.union names names'

cycles :: Graph -> Cycles
cycles graph = []

ordering :: Graph -> Either Cycles Ordering
ordering graph = case cycles graph of
  [] -> Right $ loop graph mempty
  cs -> Left cs
  where
    loop :: Graph -> Set S.GName -> Ordering
    loop graph available = -- traceShow available $
      if available == Map.keysSet graph then
        []
      else
        let nowAvailable = Map.keysSet $ Map.filter (\ds -> ds `Set.isSubsetOf` available) graph
        in (nowAvailable `Set.difference` available):(loop graph (nowAvailable `Set.union` available))

tr s f = trace s () `seq` f

checkProgram :: HasCallStack => Program -> Elab C.Program
checkProgram program = case pTraceShowId $ ordering {-$ pTraceShowId-} $ dependencies (Map.toList program) of
  Right ord -> do
    loopDeclare program ord
    program <- loopDefine program ord
    pure $ C.Program program
  Left cs -> error "Left"
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
            check ty meta >>= eval
          ProdDef ty _ -> check ty N.TypeType1 >>= eval
          IndDef ty -> check ty N.TypeType1 >>= eval
          ConDef _ ty -> check ty N.TypeType1 >>= eval
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
          vDec <- check dec meta >>= eval
          cDef <- check def vDec
          pure (C.TermDef nid cDef, vDec)
        IndDef dec -> do
          cDec <- check dec N.TypeType1
          pure (C.IndDef nid cDec, N.TypeType1)
        ProdDef dec fields -> do
          cDec <- check dec N.TypeType1
          bindParams dec
          cFields <- mapM ((flip check) N.TypeType0) fields
          pure (C.ProdDef nid cDec cFields, N.TypeType0)
          where
            bindParams :: S.Term -> Elab ()
            bindParams term = case term of
              S.Pi name inTy outTy -> do
                vInTy <- check inTy N.TypeType1 >>= eval
                bind name vInTy
                bindParams outTy
              S.U0 -> pure ()
              _ -> putError MalformedProdDec
        ConDef name ty -> do
          cTy <- check ty N.TypeType1
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
  scope case (term, goal) of
    (S.Ann term' ty, _) -> do
      cTy <- check ty univ 
      vTy <- eval cTy
      unify goal vTy
      check term' vTy
    (S.Lam names body, _) -> go names goal where
      go :: [S.Name] -> N.Value -> Elab C.Term
      go ns g = case (ns, g) of
        ([], _) -> error "Empty"
        ([n], ty@(N.FunType inTy outTy)) -> do
          cTy <- readback ty
          vOutTy <- appClosure outTy inTy
          bind n inTy
          cBody <- check body vOutTy
          pure $ C.FunIntro cBody cTy
        (n:ns, ty@(N.FunType inTy outTy)) -> do
          cTy <- readback ty
          vOutTy <- appClosure outTy inTy
          bind n inTy
          cBody <- go ns vOutTy
          pure $ C.FunIntro cBody cTy
        (_, _) -> do
          putError TooManyParams
          pure C.ElabError
    (S.Let name def defTy body, _) -> do
      reserve [name]
      vDefTy <- check defTy univ >>= eval
      cDef <- check def vDefTy
      vDef <- eval cDef
      defineReserved name vDef vDefTy
      cBody <- check body goal
      pure $ C.Letrec [cDef] cBody
    (S.Hole, _) -> freshMeta cGoal
    (S.Quote inner, N.QuoteType ty) -> do
      unify univ N.TypeType1
      putGoalUniv N.TypeType0
      cInner <- check inner ty
      cTy <- readback ty
      pure $ C.QuoteIntro cInner cTy
    (S.MkProd ty fields, N.ProdType tid _) -> do
      cTy <- check ty N.TypeType1
      vTy <- eval cTy
      unify goal vTy
      globalDefFromId tid >>= \case
        Just (C.ProdDef _ _ fieldTypes) -> do
          vFieldTypes <- mapM eval fieldTypes
          cFields <- mapM (\(f, t) -> check f t) (zip fields vFieldTypes)
          pure $ C.ProdIntro cTy cFields
    (_, N.QuoteType ty) | univ /= N.TypeType1 -> do
      putGoalUniv N.TypeType0
      (cTerm, termTy) <- infer term
      cTermTy <- readback termTy
      pure $ C.QuoteIntro cTerm cTermTy
    (_, _) -> do
      (cTerm, ty) <- infer term
      unify goal ty
      pure cTerm

infer :: HasCallStack => S.Term -> Elab (C.Term, N.Value)
infer term = getGoalUniv >>= \univ -> scope case term of
  S.Ann term' ty -> do
    vTy <- check ty univ >>= eval
    cTerm' <- check term' vTy
    pure (cTerm', vTy)
  S.Var name -> do
    entry <- localType name
    case entry of
      Just (ty, ix) -> do
        cTy <- readback ty
        pure (C.Var ix cTy, ty)
      Nothing -> do
        putError $ UnboundLocal name
        pure (C.ElabError, N.ElabError)
  S.GVar name -> do
    entry <- globalDef name
    case entry of
      Just def -> do
        ty <- case def of
          C.TermDef _ tdef -> typeofC tdef
          C.IndDef _ ty -> pure ty
          C.ConDef _ ty -> pure ty
          C.ProdDef _ ty _ -> pure ty
          C.ElabBlankItem nid ty -> pure ty
        vTy <- eval ty
        pure (C.GVar (C.itemId def) ty, vTy)
      Nothing -> do
        putError $ UnboundGlobal name
        pure (C.ElabError, N.ElabError)
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
        let ty = N.FunType vMeta closure
        pure (C.FunIntro cBody (C.FunType cMeta cBodyTy), ty)
      n:ns -> do
        cMeta <- readback univ >>= freshMeta
        vMeta <- eval cMeta
        bind n vMeta
        (cBody, vBodyTy) <- go ns
        closure <- closeValue vBodyTy
        cBodyTy <- readback vBodyTy
        let ty = N.FunType vMeta closure
        pure (C.FunIntro cBody (C.FunType cMeta cBodyTy), ty)
  S.App lam args -> do
    (cLam, lamTy) <- infer lam
    go cLam (reverse args) lamTy
    where
      go :: C.Term -> [S.Term] -> N.Value -> Elab (C.Term, N.Value)
      go cLam as lty = case (as, lty) of
        ([], _) -> error "Empty"
        ([a], N.FunType inTy outTy) -> do
          cArg <- check a inTy
          vArg <- eval cArg
          outTy <- evalClosure outTy vArg
          pure (C.FunElim cLam cArg, outTy)
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
          unify lty (N.FunType vInTy outTyClo)
          pure (C.FunElim cLam cArg, vOutTy)
        (a:as, N.FunType inTy outTy) -> do
          cArg <- check a inTy
          vArg <- eval cArg
          outTy <- evalClosure outTy vArg
          (cLamInner, outTyInner) <- go cLam as outTy
          pure (C.FunElim cLamInner cArg, outTyInner)
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
          unify lty (N.FunType vInTy outTyClo)
          (cLamInner, outTyInner) <- go cLam as vOutTy
          pure (C.FunElim cLamInner cArg, outTyInner)
  S.U0 -> do
    unify univ N.TypeType0
    pure (C.TypeType0, N.TypeType0)
  S.U1 -> do
    unify univ N.TypeType1
    pure (C.TypeType1, N.TypeType1)
  S.Pi name inTy outTy -> do
    unify univ N.TypeType1
    cInTy <- check inTy univ
    vInTy <- eval cInTy
    bind name vInTy
    cOutTy <- check outTy univ
    pure (C.FunType cInTy cOutTy, univ)
  S.Code ty -> do
    unify univ N.TypeType1
    putGoalUniv N.TypeType0
    cTy <- check ty N.TypeType0
    pure (C.QuoteType cTy, N.TypeType1)
  S.Quote inner -> do
    unify univ N.TypeType1
    putGoalUniv N.TypeType0
    (cInner, innerTy) <- infer inner
    cInnerTy <- readback innerTy
    pure (C.QuoteIntro cInner cInnerTy, N.QuoteType innerTy)
  S.Splice quote -> do
    unify univ N.TypeType0
    putGoalUniv N.TypeType1
    (cQuote, quoteTy) <- infer quote
    quoteInnerTy <- case quoteTy of
      N.QuoteType ty -> pure ty
      _ -> freshMeta C.TypeType0 >>= eval
    pure (C.QuoteElim cQuote, quoteInnerTy)
  S.MkProd ty fields -> do
    cTy <- check ty N.TypeType1
    vTy <- eval cTy
    case vTy of
      N.ProdType tid _ -> globalDefFromId tid >>= \case
        Just (C.ProdDef _ _ fieldTypes) -> do
          vFieldTypes <- mapM eval fieldTypes
          cFields <- mapM (\(f, t) -> check f t) (zip fields vFieldTypes)
          pure (C.ProdIntro cTy cFields, vTy)
      _ -> do
        putError ExpectedProdType
        pure (C.ElabError, N.ElabError)
  S.Let name def defTy body -> do
    reserve [name]
    vDefTy <- check defTy univ >>= eval
    cDef <- check def vDefTy
    vDef <- eval cDef
    defineReserved name vDef vDefTy
    (cBody, vBodyTy) <- infer body
    pure (C.Letrec [cDef] cBody, vBodyTy)
  S.Hole -> do
    cTypeMeta <- readback univ >>= freshMeta
    vTypeMeta <- eval cTypeMeta
    cTermMeta <- freshMeta cTypeMeta
    pure (cTermMeta, vTypeMeta)
  _ -> error $ "`infer`: " ++ show term

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
    { locals = (N.StuckRigidVar ty (level state) []):(locals state)
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
      C.IndDef _ ty -> ty
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
  runNorm $ N.appClosure closure (N.StuckRigidVar ty (level state) [])

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
  let meta = C.InsertedMeta (binderInfos state) (Global $ nextMeta state) ty
  put $ state
    { metas = Map.insert (Global $ nextMeta state) N.Unsolved (metas state)
    , nextMeta = (nextMeta state) + 1 }
  pure meta

freshUnivMeta :: Elab C.Term
freshUnivMeta = do
  state <- get
  let meta = C.InsertedMeta (binderInfos state) (Global $ nextMeta state) meta
  put $ state
    { metas = Map.insert (Global $ nextMeta state) N.Unsolved (metas state)
    , nextMeta = (nextMeta state) + 1 }
  pure meta 

unify :: HasCallStack => N.Value -> N.Value -> Elab ()
unify val val' = do
  state <- get
  let ((), (newMetas, newErrors, _)) = U.runUnify (U.unify (level state) val val') (metas state, [], gnameMapToIdMap (globals state))
  case newErrors of
    [] -> put $ state { metas = newMetas }
    _ -> forM_ (map UnifyError newErrors) putError

putError :: InnerError -> Elab ()
putError err = do
  state <- get
  put $ state { errors = (Error (locals state) (globals state) (level state) err):(errors state) }

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