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

data LowerState = LowerState
  { unSTGReps :: Map.Map Id RuntimeRep
  , unObjReps :: Map.Map Id RuntimeRep
  , unDecls :: [([L.Declaration], [(L.Binding, L.Term)])]
  , unNextId :: Id
  , unGlobals :: Map.Map Id Id }

data LowerContext = LowerContext
  { unLocals :: Map.Map Index Id }

type Lower sig m = (Has (State LowerState) sig m, Has (Reader LowerContext) sig m)

lower :: Lower sig m => O.Term -> m L.Term
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
lower (O.TypeType (Object rep)) = pure (L.Val (L.Univ rep))
lower (O.LocalVar ix) = L.Val <$> localVar ix
lower (O.GlobalVar did) = L.Val <$> globalVar did
lower (O.Let decls body) = do
  addDecls decls
  L.Letrec <$> filterMapM lowerDecl decls <*> lower body

lowerBind :: Lower sig m => O.Term -> m L.Value
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

funIntros :: O.Term -> ([O.Type], O.Term)
funIntros (O.FunIntro ty body) =
  let (tys, body') = funIntros body
  in (ty:tys, body')

lowerDecl :: Lower sig m => O.Declaration -> m (Maybe L.Declaration)
lowerDecl (O.Term _ sig def@(O.FunIntro _ _)) = Just <$> funDecl [] def
lowerDecl (O.Term _ _ def) = do
  name <- freshId
  lDef <- scope (lower def)
  pure (Just (L.Thunk name lDef))
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
addDecls [] = pure ()
addDecls (decl : decls) = do
  rep <- repOf (O.unSig decl)
  name <- freshId
  state <- get
  put (state
    { unSTGReps = Map.insert name rep (unSTGReps state)
    , unObjReps = Map.insert (O.unId decl) rep (unObjReps state)
    , unGlobals = Map.insert (O.unId decl) name (unGlobals state) })
  addDecls decls

repOf :: Lower sig m => O.Signature -> m RuntimeRep
repOf = undefined

repOfTerm :: Lower sig m => L.Term -> m RuntimeRep
repOfTerm = undefined

repOfDecl :: L.Declaration -> RuntimeRep
repOfDecl (L.Fun _ _ _ _) = Ptr
repOfDecl (L.Thunk _ _) = Lazy

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
  goDecl (L.Thunk _ body) bound = goTerm body bound

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

localVar :: Lower sig m => Index -> m L.Value
localVar ix = do
  locals <- unLocals <$> ask
  pure (L.Var (locals Map.! ix))

globalVar :: Lower sig m => Id -> m L.Value
globalVar did = do
  globals <- unGlobals <$> get
  pure (L.Var (globals Map.! did))

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
