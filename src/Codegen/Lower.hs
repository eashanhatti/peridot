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
  { unBindingReps :: Map.Map Id RuntimeRep -- reps from bound names
  , unTypeReps :: Map.Map Id RuntimeRep -- reps from type decl names - how the type's values are represented
  , unDecls :: [([L.Declaration], [(L.Binding, L.Term)])]
  , unNextId :: Id
  , unGlobals :: Map.Map Id Id }

data LowerContext = LowerContext
  { unLocals :: Map.Map Index Id }

type Lower sig m =
  ( Has (State LowerState) sig m
  , Has (Reader LowerContext) sig m)

lower :: HasCallStack => Lower sig m => O.Term -> m L.Term
lower (O.FunType inTy outTy) = L.Val <$> (L.Arrow <$> lowerBind inTy <*> lowerBind outTy)
lower (funIntros -> (tys@(null -> False), body)) = do
  name <- freshId
  bs <- traverse (\ty -> L.Binding <$> repOf ty <*> freshId) tys
  lBody <- lower body
  vs <- freeVars lBody
  L.Val <$> bindDecl (L.Fun name vs bs lBody)
lower (con -> Just (did, args)) = L.Val <$> (L.Con did <$> traverse lowerBind args)
lower (funElims -> (lam, args@(null -> False))) =
  scope (L.App <$> lowerBind lam <*> traverse lowerBind args)
lower (O.IOType ty) = L.Val <$> (L.IOType <$> lowerBind ty)
lower (O.IOIntro1 term) = lower term
lower (O.IOIntro2 act k) = L.DoIO act <$> lower k
lower O.UnitIntro = pure (L.Val L.Unit)
lower O.UnitType = pure (L.Val L.UnitType)
lower (O.TypeType rep) = pure (L.Val (L.Univ rep))
lower (O.LocalVar ix) = L.Val <$> localVar ix
lower (O.GlobalVar did) = flip L.App [] <$> globalVar did
lower (O.Let decls body) = do
  addDecls decls
  L.Letrec <$> filterMapM lowerDecl decls <*> lower body

lowerBind :: HasCallStack => Lower sig m => O.Term -> m L.Value
lowerBind = lower >=> bindTerm

con :: O.Term -> Maybe (Id, [O.Term])
con (O.FunElim lam arg) = do
  (did, args) <- con lam
  pure (did, args ++ [arg])
con (O.ObjectConstantIntro did) = pure (did, [])
con _ = Nothing

funElims :: O.Term -> (O.Term, [O.Term])
funElims (O.FunElim lam arg) =
  let (lam', args) = funElims lam
  in (lam', args ++ [arg])
funElims lam = (lam, [])

funIntros :: O.Term -> ([O.Type], O.Term)
funIntros (O.FunIntro ty body) =
  let (tys, body') = funIntros body
  in (ty:tys, body')
funIntros ty = ([], ty)

lowerDecl :: Lower sig m => O.Declaration -> m (Maybe L.Declaration)
lowerDecl (O.Term _ sig def@(O.FunIntro _ _)) = Just <$> funDecl [] def
lowerDecl (O.Term _ _ def) = do
  name <- freshId
  lDef <- scope (lower def)
  vs <- freeVars lDef
  pure (Just (L.Fun name vs [] lDef))
lowerDecl (O.ObjectConstant _ _) = pure Nothing

funDecl :: Lower sig m => [L.Binding] -> O.Term -> m L.Declaration
funDecl bs body = do
  name <- freshId
  lBody <- scope (lower body)
  vs <- freeVars lBody
  pure (L.Fun name vs bs lBody)
funDecl bs (O.FunIntro ty body) = do
  name <- freshId
  rep <- repOf ty
  funDecl (bs ++ [L.Binding rep name]) body

addDecls :: Lower sig m => [O.Declaration] -> m ()
addDecls decls = traverse_ go decls where
  go :: Lower sig m => O.Declaration -> m ()
  go (O.Term did _ (O.FunIntro _ _)) = do
    state <- get
    name <- freshId
    put (state
      { unBindingReps = Map.insert name Ptr (unBindingReps state)
      , unGlobals = Map.insert did name (unGlobals state) })
  go (O.Term did _ _) = do
    state <- get
    name <- freshId
    put (state
      { unBindingReps = Map.insert name Lazy (unBindingReps state)
      , unGlobals = Map.insert did name (unGlobals state) })
  go (O.ObjectConstant did (funElims -> (O.TypeType rep, _))) = do
    state <- get
    name <- freshId
    put (state
      { unTypeReps = Map.insert name rep (unTypeReps state)
      , unGlobals = Map.insert did name (unGlobals state) })
  go _ = pure ()

-- get rep from type
repOf :: HasCallStack => Lower sig m => O.Signature -> m RuntimeRep
repOf (O.FunType _ _) = pure Ptr
repOf (funElims -> (O.ObjectConstantIntro did, _)) = do
  reps <- unTypeReps <$> get
  pure (reps ! did)
repOf O.UnitType = pure Erased
repOf (O.IOType _) = pure Ptr
repOf (O.TypeType _) = pure Ptr

-- get rep from term
repOfTerm :: HasCallStack => Lower sig m => L.Term -> m RuntimeRep
repOfTerm (L.Val (L.Var name)) = do
  reps <- unBindingReps <$> get
  pure (reps ! name)
repOfTerm (L.Val (L.Con name _)) = do
  reps <- unBindingReps <$> get
  pure (reps ! name)
repOfTerm (L.Val (L.Arrow _ _)) = pure Ptr
repOfTerm (L.Val L.Unit) = pure Erased
repOfTerm (L.Val L.UnitType) = pure Ptr
repOfTerm (L.Val (L.IOType _)) = pure Ptr
repOfTerm (L.Val (L.Univ _)) = pure Ptr

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
  goVal (L.Con _ vals) bound = Set.unions <$> traverse (flip goVal bound) vals
  goVal (L.Arrow inTy outTy) bound = Set.union <$> goVal inTy bound <*> goVal outTy bound
  goVal L.Unit _ = pure mempty
  goVal L.UnitType _ = pure mempty
  goVal (L.IOType ty) bound = goVal ty bound
  goVal (L.Univ _) _ = pure mempty

bindTerm :: Lower sig m => L.Term -> m L.Value
bindTerm term = do
  state <- get
  rep <- repOfTerm term
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
  globals <- unGlobals <$> get
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
