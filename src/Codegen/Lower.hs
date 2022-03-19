module Codegen.Lower where

import Syntax.Object qualified as O
import Syntax.STG qualified as L
import Syntax.Extra
import Data.Map qualified as Map
import Data.Set qualified as Set
import Control.Effect.State
import Control.Effect.Reader
import Control.Algebra(Has)
import Control.Monad
import Data.Foldable
import GHC.Stack
import Extra

data LowerState = LowerState
  { unDecls :: [([L.Declaration], [(L.Binding, L.Term)])]
  , unNextId :: Id
  , unThunks :: Set.Set Id }

data LowerContext = LowerContext
  { unLocals :: Map.Map Index Id
  , unGlobals :: Map.Map Id Id
  , unReps :: Map.Map Index RuntimeRep }

type Lower sig m =
  ( Has (State LowerState) sig m
  , Has (Reader LowerContext) sig m)

lower :: HasCallStack => Lower sig m => O.Term -> m L.Term
lower (O.FunType inTy outTy) = L.Val <$> (L.Arrow <$> lowerBind inTy)
lower (funIntros -> (reps@(null -> False), body)) = do
  name <- freshId
  params <- traverse (const freshId) reps
  let bs = map (\(rep, param) -> L.Binding rep param) (zip reps params)
  lBody <- withLocals bs (lower body)
  vs <- Set.difference <$> freeVars lBody <*> pure (Set.fromList params)
  L.Val <$> bindDecl (L.Fun name vs bs lBody)
lower (funElims -> (lam, args@(null -> False))) =
  scope (L.App <$> lowerBind lam <*> traverse lowerBind args)
lower (O.IOType ty) = L.Val <$> (L.IOType <$> lowerBind ty)
lower (O.IOIntroPure term) = lower term
lower (O.IOIntroBind act k) = L.DoIO act <$> lower k
lower O.UnitIntro = pure (L.Val L.Unit)
lower O.UnitType = pure (L.Val L.UnitType)
lower (O.TypeType rep) = pure (L.Val (L.Univ rep))
lower (O.LocalVar ix) = L.Val <$> localVar ix
lower (O.GlobalVar did) = do
  thunks <- unThunks <$> get
  if Set.member did thunks then
    flip L.App [] <$> globalVar did
  else
    L.Val <$> globalVar did
lower (O.Let decls body) = withDecls decls \gls -> L.Letrec <$> lowerDecls decls gls <*> lower body

withDecls :: forall sig m a. Lower sig m => [O.Declaration] -> (Map.Map Id Id -> m a) -> m a
withDecls decls act = go decls mempty where
  go :: Lower sig m => [O.Declaration] -> Map.Map Id Id -> m a
  go [] acc = act acc
  go ((O.unId -> did):decls) acc = do
    name <- freshId
    local (\ctx -> ctx { unGlobals = Map.insert did name (unGlobals ctx) }) (go decls (Map.insert did name acc))

lowerDecls :: Lower sig m => [O.Declaration] -> Map.Map Id Id -> m [L.Declaration]
lowerDecls [] _ = pure []
lowerDecls (O.Term did _ _ def@(O.FunIntro _ _) : decls) gls@((! did) -> name) = do
  decl <- funDecl [] name def
  (decl :) <$> lowerDecls decls gls
lowerDecls (O.Term did _ _ def : decls) gls@((! did) -> name) = do
  lDef <- scope (lower def)
  vs <- freeVars lDef
  modify (\st -> st { unThunks = Set.insert did (unThunks st) })
  (L.Fun name vs [] lDef :) <$> lowerDecls decls gls
lowerDecls (O.ObjectConstant _ _ _ : decls) gls = lowerDecls decls gls

funDecl :: Lower sig m => [L.Binding] -> Id -> O.Term -> m L.Declaration
funDecl bs name (O.FunIntro rep body) = do
  param <- freshId
  funDecl (bs ++ [L.Binding rep param]) name body
funDecl bs name body = do
  lBody <- withLocals bs (scope (lower body))
  let params = map (\(L.Binding _ param) -> param) bs
  vs <- Set.difference <$> freeVars lBody <*> pure (Set.fromList params)
  pure (L.Fun name vs bs lBody)

lowerBind :: HasCallStack => Lower sig m => O.Term -> m L.Value
lowerBind term = do
  lTerm <- lower term
  rep <- repOf term
  bindTerm lTerm rep

repOf :: HasCallStack => Lower sig m => O.Term -> m RuntimeRep
repOf (O.FunType _ _) = pure Ptr
repOf (O.FunIntro _ _) = pure Ptr
repOf (O.FunElim _ _ rep) = pure rep
repOf (O.IOType _) = pure Ptr
repOf (O.IOIntroPure _) = pure Ptr
repOf (O.IOIntroBind _ _) = pure Ptr
repOf O.UnitType = pure Ptr
repOf O.UnitIntro = pure Erased
repOf (O.TypeType _) = pure Ptr
repOf (O.LocalVar ix) = (! ix) <$> (unReps <$> ask)
repOf (O.GlobalVar _) = pure Ptr

withLocals :: Lower sig m => [L.Binding] -> m a -> m a
withLocals [] act = act
withLocals (L.Binding rep did : bs) act =
  local
    (\ctx -> ctx
      { unReps = Map.insert 0 rep (Map.mapKeys (\k -> k + 1) (unReps ctx))
      , unLocals = Map.insert 0 did (Map.mapKeys (\k -> k + 1) (unLocals ctx)) })
    (withLocals bs act)

withGlobals :: Lower sig m => [(Id, Id)] -> m a -> m a
withGlobals [] act = act
withGlobals ((did, name):ds) act = local (\ctx -> ctx { unGlobals = Map.insert did name (unGlobals ctx) }) (withGlobals ds act)
-- con :: O.Term -> Maybe (Id, [O.Term])
-- con (O.FunElim lam arg) = do
--   (did, args) <- con lam
--   pure (did, args ++ [arg])
-- con (O.ObjectConstantIntro did) = pure (did, [])
-- con _ = Nothing

funElims :: O.Term -> (O.Term, [O.Term])
funElims (O.FunElim lam arg _) =
  let (lam', args) = funElims lam
  in (lam', args ++ [arg])
funElims lam = (lam, [])

funIntros :: O.Term -> ([RuntimeRep], O.Term)
funIntros (O.FunIntro rep body) =
  let (reps, body') = funIntros body
  in (rep:reps, body')
funIntros body = ([], body)

repOfDecl :: L.Declaration -> RuntimeRep
repOfDecl (L.Fun _ _ _ _) = Ptr

filterMapM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
filterMapM f [] = pure []
filterMapM f (x:xs) = do
  mx <- f x
  case mx of
    Just mx -> (mx :) <$> filterMapM f xs
    Nothing -> filterMapM f xs

freshId :: Lower sig m => m Id
freshId = do
  state <- get
  put (state { unNextId = unNextId state + 1 })
  pure (unNextId state)

freeVars :: Lower sig m => L.Term -> m (Set.Set Id)
freeVars term = goTerm term mempty where
  goTerm :: Lower sig m => L.Term -> Set.Set Id -> m (Set.Set Id)
  goTerm (L.App lam args) bound = Set.union <$> goVal lam bound <*> (Set.unions <$> traverse (flip goVal bound) args)
  goTerm (L.Letrec decls body) bound = Set.union <$> (Set.unions <$> traverse (flip goDecl bound) decls) <*> goTerm body bound
  goTerm (L.Let bs body) bound = Set.union <$> (Set.unions <$> traverse (flip goTerm bound) (map snd bs)) <*> goTerm body bound
  goTerm (L.DoIO _ k) bound = goTerm k bound
  goTerm (L.Val val) bound = goVal val bound

  goDecl :: Lower sig m => L.Declaration -> Set.Set Id -> m (Set.Set Id)
  goDecl (L.Fun _ _ _ body) bound = goTerm body bound

  goVal :: Lower sig m => L.Value -> Set.Set Id -> m (Set.Set Id)
  goVal (L.Var name) bound = do
    if Set.member name bound then
      pure mempty
    else
      pure (Set.singleton name)
  goVal (L.Arrow inTy) bound = goVal inTy bound
  goVal L.Unit _ = pure mempty
  goVal L.UnitType _ = pure mempty
  goVal (L.IOType ty) bound = goVal ty bound
  goVal (L.Univ _) _ = pure mempty

bindTerm :: Lower sig m => L.Term -> RuntimeRep -> m L.Value
bindTerm term rep = do
  state <- get
  let (decls, terms):scopes = unDecls state
  name <- freshId
  put (state { unDecls = (decls, (L.Binding rep name, term):terms):scopes })
  pure (L.Var name)

bindDecl :: Lower sig m => L.Declaration -> m L.Value
bindDecl decl = do
  state <- get
  let (decls, terms):scopes = unDecls state
  put (state { unDecls = (decl:decls, terms):scopes })
  pure (L.Var (L.unName decl))

localVar :: HasCallStack => Lower sig m => Index -> m L.Value
localVar ix = do
  locals <- unLocals <$> ask
  pure (L.Var (locals ! ix))

globalVar :: HasCallStack => Lower sig m => Id -> m L.Value
globalVar did = do
  globals <- unGlobals <$> ask
  pure (L.Var (globals ! did))

scope :: Lower sig m => m L.Term -> m L.Term
scope act = do
  state <- get
  put (state { unDecls = ([], []) : unDecls state })
  term <- act
  state' <- get
  when (length (unDecls state') /= 1 + length (unDecls state)) (error "Bug: `scope`")
  let (decls, bs):scopes = unDecls state'
  put (state' { unDecls = tail (unDecls state') })
  pure (L.Letrec decls (L.Let bs term))
