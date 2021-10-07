{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
-- {-# OPTIONS_GHC -fdefer-type-errors #-}

module Elaboration where

import qualified Data.Map as Map
import qualified Norm as N
import qualified Unification as U
import qualified Surface as S
import qualified Core as C
import Var
import Control.Monad.State(State, get, put, runState)
import Control.Monad(forM_)
import Control.Monad.Reader(runReader, Reader, ask, local)
import Debug.Trace
import qualified Data.Set as Set
import Data.Set(singleton, Set)
import qualified Data.Map as Map
import Data.Map(Map)
import Debug.Trace
import GHC.Stack
import Prelude hiding(Ordering)
import Debug.Pretty.Simple(pTraceShowId, pTrace)

data InnerError = UnboundName S.Name | UnifyError U.Error
  deriving Show

data Error = Error S.Span N.Locals Level InnerError

instance Show Error where
  show (Error s ls lv e) = "Error\n" ++ show e ++ "\n" ++ indent "  " (show lv) ++ indent "  " stringLocals
    where
      indent :: String -> String -> String
      indent i s = unlines $ map (i++) (lines s)

      stringLocals :: String
      stringLocals = concat $ map (\l -> show l ++ "\n") ls

data ElabState = ElabState
  { metas :: N.Metas
  , nextMeta :: Int
  , goalUniv :: N.Value
  , errors :: [Error]
  , locals :: N.Locals
  , ltypes :: Map.Map S.Name (N.Value, Index)
  , level :: Level
  , sourceSpan :: S.Span
  , binderInfos :: [C.BinderInfo]
  , nextName :: Int
  , reservedNames :: [S.Name] }
  deriving Show

type Elab a = State ElabState a

data Item
  = TermDef S.GName S.Term S.Term
  | IndDef S.GName S.Term [(S.GName, S.Term)]

elab :: HasCallStack => S.Item -> (C.Program, ElabState)
elab item = runState (checkTl (flatten [] item)) (ElabState mempty 0 N.TypeType1 [] [] mempty (Level 0) S.Span [] 0 [])

flatten :: [String] -> S.Item -> [Item]
flatten gname item = case item of
  S.NamespaceDef name items -> concat $ map (flatten ((S.unName name):gname)) items
  S.TermDef name dec def -> [TermDef (S.GName $ (S.unName name):gname) dec def]
  S.IndDef name dec cs -> [IndDef (S.GName $ (S.unName name):gname) dec (map (\(cn, ct) -> (S.GName $ (S.unName cn):(S.unName name):gname, ct)) cs)]

type Graph = Map S.GName (Set S.GName)
type Cycles = [(S.GName, [S.GName])]
type Ordering = [Set S.GName]

dependencies :: [Item] -> Graph
dependencies items = case items of
  item:items ->
    let
      ds = case item of
        TermDef name dec def -> Map.singleton name (searchTy dec `Set.union` search def)
        IndDef name dec cs -> Map.singleton name (searchTy dec `Set.union` foldl Set.union mempty (map searchTy (map snd cs)))
    in ds `Map.union` dependencies items
  [] -> mempty
  where
    search term = runReader (search' term) False
    searchTy term = runReader (search' term) True

    search' :: S.Term -> Reader Bool (Set S.GName)
    search' term = case term of
      S.Spanned term _ -> search' term
      S.Var _ -> pure mempty
      S.GVar (S.GName name) -> ask >>= \b -> pure $ if b then singleton (S.GName $ reverse name) else mempty
      S.Lam _ body -> search' body
      S.App lam arg -> Set.union <$> search' lam <*> search' arg
      S.Ann _ ty -> local (const True) $ search' ty
      S.Pi _ inTy outTy -> Set.union <$> search' inTy <*> search' outTy
      S.Let _ def defTy body -> Set.union <$> search' def <*> (Set.union <$> (local (const True) $ search' defTy) <*> search' body)
      S.U0 -> pure mempty
      S.U1 -> pure mempty
      S.Code term -> search' term
      S.Quote term -> search' term
      S.Splice term -> search' term
      S.Hole -> pure mempty

cycles :: Graph -> Cycles
cycles graph = []

loop :: Graph -> Set S.GName -> Ordering
loop graph available = -- traceShow available $
  if available == Map.keysSet graph then
    []
  else
    let nowAvailable = Map.keysSet $ Map.filter (\ds -> ds `Set.isSubsetOf` available) graph
    in (nowAvailable `Set.difference` available):(loop graph (nowAvailable `Set.union` available))

ordering :: Graph -> Either Cycles Ordering
ordering graph = case cycles graph of
  [] -> Right $ loop graph mempty
  cs -> Left cs

checkTl :: [Item] -> Elab C.Program
checkTl items = case ordering (pTraceShowId $ dependencies items) of
  Right ord -> pTrace ("Ordering = " ++ show ord) undefined
  Left cs -> undefined

check :: HasCallStack => S.Term -> N.Value -> Elab C.Term
check term goal = do
  -- let !() = trace ("Goal = " ++ show goal) ()
  goal <- force goal
  -- let !() = trace ("Term = " ++ show term) ()
  -- let !() = trace ("FGoal = " ++ show goal) ()
  cGoal <- readback goal
  univ <- getGoalUniv
  -- let !() = trace ("CGoal = " ++ show cGoal) ()
  scope $ case (term, goal) of
    (S.Spanned term' ssp, _) -> do
      putSpan ssp
      check term' goal
    (S.Ann term' ty, _) -> do
      cTy <- check ty univ 
      vTy <- eval cTy
      unify goal vTy
      check term' vTy
    (S.Lam name body, (N.FunType inTy outTy)) -> do
      vOutTy <- appClosure outTy inTy
      bind name inTy
      cBody <- check body vOutTy
      pure $ C.FunIntro cBody cGoal
    -- (S.Let name def defTy body, _) -> do
    --   -- TODO: reduce `<-` clutter
    --   cDefTy <- check defTy univ
    --   vDefTy <- eval cDefTy
    --   cDef <- check def vDefTy
    --   vDef <- eval cDef
    --   define name vDef vDefTy
    --   cBody <- check body goal
    --   pure $ C.Let cDef cDefTy cBody
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
    (_, N.QuoteType ty) | univ /= N.TypeType1 -> do
      univMeta <- freshUnivMeta >>= eval
      putGoalUniv univMeta
      (cTerm, termTy) <- infer term
      case termTy of
        N.QuoteType ty' -> do
          unify univMeta N.TypeType1
          pure cTerm
        _ -> do
          unify univMeta N.TypeType0
          cTermTy <- readback termTy
          pure $ C.QuoteIntro cTerm cTermTy
    (_, _) -> do
      (cTerm, ty) <- infer term
      unify goal ty
      pure cTerm

infer :: HasCallStack => S.Term -> Elab (C.Term, N.Value)
infer term = getGoalUniv >>= \univ -> scope $ case term of
  S.Spanned term' ssp -> do
    putSpan ssp
    infer term'
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
        putError $ UnboundName name
        pure (C.ElabError, N.ElabError)
  S.Lam name body -> do
    -- TODO: reduce `<-` clutter
    cMeta <- readback univ >>= freshMeta
    vMeta <- eval cMeta
    (cBody, vBodyTy) <- {-scope-} do
      bind name vMeta
      infer body
    closure <- closeValue vBodyTy
    cBodyTy <- readback vBodyTy
    let ty = N.FunType vMeta closure
    pure (C.FunIntro cBody (C.FunType cMeta cBodyTy), ty)
  S.App lam arg -> do
    state <- get
    (cLam, lamTy) <- infer lam
    lamTy <- force lamTy
    -- let !() = trace ("Lam Type = " ++ show lamTy) ()
    (cLam, cArg, inTy, outTy) <- scope $ case lamTy of
      N.FunType inTy outTy -> do
        cArg <- check arg inTy
        -- bis <- binderInfos <$> get
        -- let !() = trace ("BIs = " ++ show ) ()
        -- let !() = trace ("    cArg = " ++ show cArg) ()
        vArg <- eval cArg
        outTy <- evalClosure outTy vArg
        pure (cLam, cArg, inTy, outTy)
      _ -> do
        inTy <- readback univ >>= freshMeta
        vInTy <- eval inTy
        cArg <- check arg vInTy
        vArg <- eval cArg
        name <- freshName "x"
        -- define name vArg inTy
        outTy <- scope $ do
          bind name vInTy
          readback univ >>= freshMeta
        vOutTyClo <- closeTerm outTy
        unify lamTy (N.FunType vInTy vOutTyClo)
        define name vArg vInTy
        vOutTy <- eval outTy
        pure (cLam, cArg, vInTy, vOutTy)
    pure (C.FunElim cLam cArg, outTy)
  S.U0 -> do
    unify univ N.TypeType0
    pure (C.TypeType0, N.TypeType0)
  S.U1 -> do
    unify univ N.TypeType1
    pure (C.TypeType1, N.TypeType1)
  S.Pi name inTy outTy -> do
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
  -- S.Let name def defTy body -> do
  --   -- TODO: reduce `<-` clutter
  --   cDefTy <- check defTy univ
  --   vDefTy <- eval cDefTy
  --   cDef <- check def vDefTy
  --   vDef <- eval cDef
  --   define name vDef vDefTy
  --   (cBody, vBodyTy) <- infer body
  --   pure (C.Let cDef cDefTy cBody, vBodyTy)
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

runNorm :: HasCallStack => N.Norm a -> Elab a
runNorm act = do
  state <- get
  pure $ runReader act (level state, metas state, locals state)

force :: N.Value -> Elab N.Value
force val = do
  state <- get
  runNorm $ N.force val

-- FIXME: better name
scope :: Elab a -> Elab a
scope act = do
  state <- get
  let (a, s) = runState act state
  put $ state { metas = metas s, errors = errors s, nextMeta = nextMeta s, nextName = nextName s }
  pure a

putSpan :: S.Span -> Elab ()
putSpan ssp = do
  state <- get
  put $ state { sourceSpan = ssp }

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

readback :: N.Value -> Elab C.Term
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

unify :: N.Value -> N.Value -> Elab ()
unify val val' = do
  state <- get
  let ((), (newMetas, newErrors)) = U.runUnify (U.unify (level state) val val') (metas state, [])
  case newErrors of
    [] -> put $ state { metas = newMetas }
    _ -> forM_ (map UnifyError newErrors) putError

putError :: InnerError -> Elab ()
putError err = do
  state <- get
  put $ state { errors = (Error (sourceSpan state) (locals state) (level state) err):(errors state) }

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

typeOf :: N.Value -> Elab N.Value
typeOf val = do
  state <- get
  pure $ U.getVty (metas state) (level state) val