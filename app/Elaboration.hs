{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BangPatterns #-}

module Elaboration where

import qualified Data.Map as Map
import qualified Eval as E
import qualified Unification as U
import qualified Surface as S
import qualified Core as C
import Var
import Control.Monad.State(State, get, put, runState)
import Control.Monad(forM_)
import Debug.Trace

data Error = UnboundName S.Name | UnifyError U.Error
  deriving Show

data ElabState = ElabState
  { metas :: E.Metas
  , nextMeta :: Int
  , errors :: [(S.Span, Error)]
  , locals :: E.Locals
  , ltypes :: Map.Map S.Name (E.Value, Index)
  , level :: Level
  , sourceSpan :: S.Span
  , binderInfos :: [C.BinderInfo]
  , nextName :: Int }
  deriving Show

type Elab a = State ElabState a

elab :: S.Term -> E.Value -> (C.Term, ElabState)
elab term goal = runState (check term goal) (ElabState Map.empty 0 [] [] Map.empty (Level 0) S.Span [] 0)

check :: S.Term -> E.Value -> Elab C.Term
check term goal = do
  goal <- force goal
  cGoal <- readback goal
  scope $ case (term, goal) of
    (S.Spanned term' ssp, _) -> do
      setspan ssp
      check term' goal
    (S.Ann term' ty, _) -> do
      cTy <- check ty E.TypeType
      vTy <- eval cTy
      unify goal vTy
      check term' vTy
    (S.Lam name body, (E.FunType inTy outTy)) -> do
      vOutTy <- appClosure outTy inTy
      bind name inTy
      cBody <- check body vOutTy
      pure $ C.FunIntro cBody cGoal
    (S.Let name def defTy body, _) -> do
      -- TODO: reduce `<-` clutter
      cDefTy <- check defTy E.TypeType
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

infer :: S.Term -> Elab (C.Term, E.Value)
infer term = scope $ case term of
  S.Spanned term' ssp -> do
    setspan ssp
    infer term'
  S.Ann term' ty -> do
    cTy <- check ty E.TypeType
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
        pure (C.ElabError, E.ElabError)
  S.Lam name body -> do
    -- TODO: reduce `<-` clutter
    cMeta <- freshMeta C.TypeType
    vMeta <- eval cMeta
    (cBody, vBodyTy) <- {-scope-} do
      bind name vMeta
      infer body
    closure <- closeValue vBodyTy
    cBodyTy <- readback vBodyTy
    let ty = E.FunType vMeta closure
    pure (C.FunIntro cBody (C.FunType cMeta cBodyTy), ty)
  S.App lam arg -> do
    state <- get
    (cLam, lamTy) <- infer lam
    lamTy <- force lamTy
    (cArg, inTy, outTy) <- scope $ case lamTy of
      E.FunType inTy outTy -> do
        cArg <- check arg inTy
        vArg <- eval cArg
        outTy <- evalClosure outTy vArg
        pure (cArg, inTy, outTy) 
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
        unify lamTy (E.FunType vInTy vOutTyClo)
        define name vArg vInTy
        vOutTy <- eval outTy
        pure (cArg, vInTy, vOutTy)
    pure (C.FunElim cLam cArg, outTy)
    -- (cLam, lamTy) <- infer lam
    -- lamTy <- force lamTy
    -- (inTy, outTy) <- case lamTy of
    --   E.FunType inTy outTy -> pure (inTy, outTy)
    --   _ -> do
    --     inTy <- freshMeta C.TypeType
    --     vInTy <- eval inTy
    --     name <- freshName "x"
    --     bind name vInTy
    --     outTy <- freshMeta C.TypeType
    --     vOutTy <- closeTerm outTy
    --     unify lamTy (E.FunType vInTy vOutTy)
    --     pure (vInTy, vOutTy)
    -- cArg <- check arg inTy
    -- vArg <- eval cArg
    -- retTy <- evalClosure outTy vArg
    -- pure (C.FunElim cLam cArg, retTy)
  S.Universe -> pure (C.TypeType, E.TypeType)
  S.Pi name inTy outTy -> do
    cInTy <- check inTy E.TypeType
    vInTy <- eval cInTy
    bind name vInTy
    cOutTy <- check outTy E.TypeType
    pure (C.FunType cInTy cOutTy, E.TypeType)
  S.Let name def defTy body -> do
    -- TODO: reduce `<-` clutter
    cDefTy <- check defTy E.TypeType
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

force :: E.Value -> Elab E.Value
force val = do
  state <- get
  pure $ E.force (metas state) val

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

bind :: S.Name -> E.Value -> Elab ()
bind name ty = do
  state <- get
  put $ state
    { locals = (E.StuckRigidVar ty (level state) []):(locals state)
    , ltypes = Map.insert name (ty, Index 0) $ Map.map (\(ty, ix) -> (ty, Index $ unIndex ix + 1)) (ltypes state)
    , level = Level $ unLevel (level state) + 1
    , binderInfos = C.Abstract:(binderInfos state) }

define :: S.Name -> E.Value -> E.Value -> Elab ()
define name def ty = do
  state <- get
  put $ state
    { locals = def:(locals state)
    , ltypes = Map.insert name (ty, Index 0) $ Map.map (\(ty, ix) -> (ty, Index $ unIndex ix + 1)) (ltypes state)
    , level = Level $ unLevel (level state) + 1
    , binderInfos = C.Concrete:(binderInfos state) }

localType :: S.Name -> Elab (Maybe (E.Value, Index))
localType name = do
  state <- get
  pure $ Map.lookup name (ltypes state)

appClosure :: E.Closure -> E.Value -> Elab E.Value
appClosure closure ty = do
  state <- get
  pure $ E.appClosure (metas state) closure (E.StuckRigidVar ty (level state) [])

-- FIXME: better name
evalClosure :: E.Closure -> E.Value -> Elab E.Value
evalClosure closure def = do
  state <- get
  pure $ E.appClosure (metas state) closure def

closeValue :: E.Value -> Elab E.Closure
closeValue value = do
  state <- get
  term <- readback value
  pure $ E.Closure (locals state) term

closeTerm :: C.Term -> Elab E.Closure
closeTerm term = do
  state <- get
  pure $ E.Closure (locals state) term

readback :: E.Value -> Elab C.Term
readback val = do
  state <- get
  pure $ E.readback (metas state) (level state) val

eval :: C.Term -> Elab E.Value
eval term = do
  state <- get
  pure $ E.eval (metas state) (locals state) term

freshMeta :: C.Term -> Elab C.Term
freshMeta ty = do
  state <- get
  let meta = C.InsertedMeta (binderInfos state) (Global $ nextMeta state) ty
  put $ state
    { metas = Map.insert (Global $ nextMeta state) E.Unsolved (metas state)
    , nextMeta = (nextMeta state) + 1 }
  pure meta

unify :: E.Value -> E.Value -> Elab ()
unify val val' = do
  state <- get
  let ((), (newMetas, newErrors)) = runState (U.unify (level state) val val') (metas state, [])
  case newErrors of
    [] -> put $ state { metas = newMetas }
    _ -> forM_ (map UnifyError newErrors) putError

putError :: Error -> Elab ()
putError err = do
  state <- get
  put $ state { errors = (sourceSpan state, err):(errors state) }

freshName :: String -> Elab S.Name
freshName base = do
  state <- get
  let n = nextName state
  put $ state { nextName = nextName state + 1 }
  pure $ S.Name (base ++ show n)