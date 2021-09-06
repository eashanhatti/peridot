{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BangPatterns #-}
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
import Control.Monad.Reader(runReader)
import Debug.Trace
import Data.Set(singleton)
import Debug.Trace
import GHC.Stack

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
  , stageMetas :: N.StageMetas
  , nextMeta :: Int
  , errors :: [Error]
  , locals :: N.Locals
  , ltypes :: Map.Map S.Name (N.Value, Index)
  , level :: Level
  , sourceSpan :: S.Span
  , binderInfos :: [C.BinderInfo]
  , nextName :: Int }
  deriving Show

type Elab a = State ElabState a

elab :: HasCallStack => S.Term -> N.Value -> (C.Term, ElabState)
elab term goal = runState (check term goal) (ElabState Map.empty Map.empty 0 [] [] Map.empty (Level 0) S.Span [] 0)

check :: HasCallStack => S.Term -> N.Value -> Elab C.Term
check term goal = do
  -- let !() = trace ("Goal = " ++ show goal) ()
  goal <- force goal
  -- let !() = trace ("Term = " ++ show term) ()
  -- let !() = trace ("FGoal = " ++ show goal) ()
  cGoal <- readback goal
  -- let !() = trace ("CGoal = " ++ show cGoal) ()
  scope $ case (term, goal) of
    (term, N.StagedType innerTy stage) -> do
      cInnerTy <- readback innerTy
      cTerm <- check term innerTy
      pure $ C.StagedIntro cTerm cInnerTy stage
    (S.Spanned term' ssp, _) -> do
      setspan ssp
      check term' goal
    (S.Ann term' ty, _) -> do
      cTy <- check ty N.TypeType
      vTy <- eval cTy
      unify goal vTy
      check term' vTy
    (S.Lam name body, (N.FunType inTy outTy)) -> do
      vOutTy <- appClosure outTy inTy
      bind name inTy
      cBody <- check body vOutTy
      pure $ C.FunIntro cBody cGoal
    (S.Let name def defTy body, _) -> do
      -- TODO: reduce `<-` clutter
      cDefTy <- check defTy N.TypeType
      vDefTy <- eval cDefTy
      cDef <- check def vDefTy
      vDef <- eval cDef
      define name vDef vDefTy
      cBody <- check body goal
      pure $ C.Let cDef cDefTy cBody
    (S.Hole, _) -> do
      freshMeta cGoal
    (_, _) -> do
      (cTerm, ty) <- infer term
      unify goal ty
      pure cTerm

infer :: HasCallStack => S.Term -> Elab (C.Term, N.Value)
infer term = scope $ case term of
  S.Spanned term' ssp -> do
    setspan ssp
    infer term'
  S.Ann term' ty -> do
    cTy <- check ty N.TypeType
    vTy <- eval cTy
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
    cMeta <- freshMeta C.TypeType
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
        vArg <- eval cArg
        outTy <- evalClosure outTy vArg
        pure (cLam, cArg, inTy, outTy)
      N.StagedType innerLamTy@(N.FunType inTy outTy) s -> do
        cArg <- check arg inTy
        vArg <- eval cArg
        outTy <- evalClosure outTy vArg
        cInnerLamTy <- readback innerLamTy
        {-let cInnerLamTy' = runReader (C.shift mempty cInnerLamTy) 1-}
        pure (C.StagedElim cLam cInnerLamTy (C.Var (Index 0) cInnerLamTy{-'-}) s, cArg, inTy, outTy)
      _ -> do
        inTy <- freshMeta C.TypeType
        vInTy <- eval inTy
        cArg <- check arg vInTy
        vArg <- eval cArg
        name <- freshName "x"
        -- define name vArg inTy
        outTy <- scope $ do
          bind name vInTy
          freshMeta C.TypeType
        vOutTyClo <- closeTerm outTy
        unify lamTy (N.FunType vInTy vOutTyClo)
        define name vArg vInTy
        vOutTy <- eval outTy
        pure (cLam, cArg, vInTy, vOutTy)
    pure (C.FunElim cLam cArg, outTy)
  S.QuoteType innerTy stage -> do
    cInnerTy <- check innerTy N.TypeType
    pure (C.StagedType cInnerTy stage, N.TypeType)
  S.Universe -> pure (C.TypeType, N.TypeType)
  S.Pi name inTy outTy -> do
    cInTy <- check inTy N.TypeType
    vInTy <- eval cInTy
    bind name vInTy
    cOutTy <- check outTy N.TypeType
    pure (C.FunType cInTy cOutTy, N.TypeType)
  S.Let name def defTy body -> do
    -- TODO: reduce `<-` clutter
    cDefTy <- check defTy N.TypeType
    vDefTy <- eval cDefTy
    cDef <- check def vDefTy
    vDef <- eval cDef
    define name vDef vDefTy
    (cBody, vBodyTy) <- infer body
    pure (C.Let cDef cDefTy cBody, vBodyTy)
  S.Hole -> do
    cTypeMeta <- freshMeta C.TypeType
    vTypeMeta <- eval cTypeMeta
    cTermMeta <- freshMeta cTypeMeta
    pure (cTermMeta, vTypeMeta)

runNorm :: HasCallStack => N.Norm a -> Elab a
runNorm act = do
  state <- get
  pure $ runReader act (level state, metas state, singleton C.T, locals state)

force :: N.Value -> Elab N.Value
force val = do
  state <- get
  runNorm $ N.force val

-- FIXME: better name
scope :: Elab a -> Elab a
scope act = do
  state <- get
  let (a, s) = runState act state
  put $ state { metas = metas s, stageMetas = stageMetas s, errors = errors s, nextMeta = nextMeta s, nextName = nextName s }
  pure a

setspan :: S.Span -> Elab ()
setspan ssp = do
  state <- get
  put $ state { sourceSpan = ssp }

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

eval :: C.Term -> Elab N.Value
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

freshStageMeta :: Elab C.Stage
freshStageMeta = do
  state <- get
  let meta = C.StageMeta (Global $ nextMeta state)
  put $ state
    { stageMetas = Map.insert (Global $ nextMeta state) N.Unsolved (stageMetas state)
    , nextMeta = (nextMeta state) + 1 }
  pure meta

unify :: N.Value -> N.Value -> Elab ()
unify val val' = do
  state <- get
  let ((), (newMetas, newStageMetas, newErrors)) = U.runUnify (U.unify (level state) val val') (metas state, stageMetas state, [])
  case newErrors of
    [] -> put $ state { metas = newMetas, stageMetas = newStageMetas }
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