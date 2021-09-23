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
elab term goal = runState (check term goal (U.getVty mempty (Level 0) goal)) (ElabState mempty 0 [] [] mempty (Level 0) S.Span [] 0)

check :: HasCallStack => S.Term -> N.Value -> N.Value -> Elab C.Term
check term goal univ = do
  -- let !() = trace ("Goal = " ++ show goal) ()
  goal <- force goal
  -- let !() = trace ("Term = " ++ show term) ()
  -- let !() = trace ("FGoal = " ++ show goal) ()
  cGoal <- readback goal
  -- let !() = trace ("CGoal = " ++ show cGoal) ()
  scope $ case (term, goal) of
    (S.Spanned term' ssp, _) -> do
      setspan ssp
      check term' goal univ
    (S.Ann term' ty, _) -> do
      cTy <- check ty univ univ
      vTy <- eval cTy
      unify goal vTy
      check term' vTy univ
    (S.Lam name body, (N.FunType inTy outTy)) -> do
      vOutTy <- appClosure outTy inTy
      bind name inTy
      cBody <- check body vOutTy univ
      pure $ C.FunIntro cBody cGoal
    (S.Let name def defTy body, _) -> do
      -- TODO: reduce `<-` clutter
      cDefTy <- check defTy univ univ
      vDefTy <- eval cDefTy
      cDef <- check def vDefTy univ
      vDef <- eval cDef
      define name vDef vDefTy
      cBody <- check body goal univ
      pure $ C.Let cDef cDefTy cBody
    (S.Hole, _) -> do
      freshMeta cGoal
    (_, _) -> do
      (cTerm, ty) <- infer term univ
      unify goal ty
      pure cTerm

infer :: HasCallStack => S.Term -> N.Value -> Elab (C.Term, N.Value)
infer term univ = scope $ case term of
  S.Spanned term' ssp -> do
    setspan ssp
    infer term' univ
  S.Ann term' ty -> do
    vTy <- check ty univ univ >>= eval
    cTerm' <- check term' vTy univ
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
      infer body univ
    closure <- closeValue vBodyTy
    cBodyTy <- readback vBodyTy
    let ty = N.FunType vMeta closure
    pure (C.FunIntro cBody (C.FunType cMeta cBodyTy), ty)
  S.App lam arg -> do
    state <- get
    (cLam, lamTy) <- infer lam univ
    lamTy <- force lamTy
    -- let !() = trace ("Lam Type = " ++ show lamTy) ()
    (cLam, cArg, inTy, outTy) <- scope $ case lamTy of
      N.FunType inTy outTy -> do
        cArg <- check arg inTy univ
        -- bis <- binderInfos <$> get
        -- let !() = trace ("BIs = " ++ show ) ()
        -- let !() = trace ("    cArg = " ++ show cArg) ()
        vArg <- eval cArg
        outTy <- evalClosure outTy vArg
        pure (cLam, cArg, inTy, outTy)
      _ -> do
        inTy <- readback univ >>= freshMeta
        vInTy <- eval inTy
        cArg <- check arg vInTy univ
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
    unify N.TypeType0 univ
    pure (C.TypeType0, N.TypeType0)
  S.U1 -> do
    unify N.TypeType1 univ
    pure (C.TypeType1, N.TypeType1)
  S.Pi name inTy outTy -> do
    cInTy <- check inTy univ univ
    vInTy <- eval cInTy
    bind name vInTy
    cOutTy <- check outTy univ univ
    pure (C.FunType cInTy cOutTy, univ)
  S.Let name def defTy body -> do
    -- TODO: reduce `<-` clutter
    cDefTy <- check defTy univ univ
    vDefTy <- eval cDefTy
    cDef <- check def vDefTy univ
    vDef <- eval cDef
    define name vDef vDefTy
    (cBody, vBodyTy) <- infer body univ
    pure (C.Let cDef cDefTy cBody, vBodyTy)
  S.Hole -> do
    cTypeMeta <- readback univ >>= freshMeta
    vTypeMeta <- eval cTypeMeta
    cTermMeta <- freshMeta cTypeMeta
    pure (cTermMeta, vTypeMeta)

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

typeOf :: N.Value -> Elab N.Value
typeOf val = do
  state <- get
  pure $ U.getVty (metas state) (level state) val