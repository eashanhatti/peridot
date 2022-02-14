module Elaboration.Effect where

import Control.Effect.State(State, get, put)
import Control.Effect.Reader(Reader, ask, local)
import Control.Effect.Throw(Throw)
import Control.Algebra(Has)
import Data.Set(Set, singleton)
import Data.Map(Map, (!), insert, union, fromList)
import Syntax.Variable hiding (unId)
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Telescope qualified as T
import Syntax.Surface
import Syntax.Stage
import Data.Some
import Data.Dependent.HashMap qualified as DMap
import Data.Dependent.HashMap(DHashMap)
import Data.Functor.Identity
import Data.GADT.Compare
import Data.Type.Equality
import Data.Hashable
import GHC.Generics hiding (Constructor)
import Normalization
import Numeric.Natural

data QueryState = QueryState
  { unMemoTable :: DHashMap Key Identity }

data Error
  = TooManyParams
  | WrongAppArity Natural Natural

type Query sig m = Has (State QueryState) sig m

data Key a where
  ElabDecl :: Predeclaration -> Key C.Declaration
  ElabTerm :: TermAst -> Key C.Term

instance GEq Key where
  geq (ElabDecl _) (ElabDecl _) = Just Refl
  geq (ElabTerm _) (ElabTerm _) = Just Refl
  geq _ _ = Nothing

instance Hashable (Some Key) where
  hashWithSalt salt (Some (ElabDecl (PDDecl (DeclAst _ did)))) = salt `hashWithSalt` did
  hashWithSalt salt (Some (ElabDecl (PDDecl (ConstrAst _ did _)))) = salt `hashWithSalt` did
  hashWithSalt salt (Some (ElabTerm (TermAst _ did))) = salt `hashWithSalt` did

memo :: Query sig m => Key a -> m a -> m a
memo key act = do
  state <- get
  case DMap.lookup key (unMemoTable state) of
    Just (Identity result) -> pure result
    Nothing -> do
      result <- act
      put (state { unMemoTable = DMap.insert key (Identity result) (unMemoTable state) })
      pure result

data Binding = BLocal Index N.Term | BGlobal Id

data ElabContext = ElabContext
  { unBindings :: Map Name Binding }

data Predeclaration = PDDecl DeclarationAst | PDConstr ConstructorAst

data ElabState = ElabState
  { unDecls :: Map Id Predeclaration
  , unDeclTypes :: Map Id N.Term
  , unUVs :: Map Global N.Term
  , unStageUVs :: Map Global (Maybe Stage)
  , unTypeUVs :: Map Global (Maybe N.Term)
  , unNextUV :: Global }

type Elab sig m = (MonadFail m, Has (Reader ElabContext) sig m, Has (State ElabState) sig m, Norm sig m, Query sig m, Has (Throw ()) sig m)

unify :: Elab sig m => N.Term -> N.Term -> m ()
unify = undefined

bindLocal :: Elab sig m => Name -> N.Term -> m a -> m a
bindLocal name ty act =
  local
    (\ctx -> ctx { unBindings = insert name (BLocal (Index 0) ty) (fmap inc (unBindings ctx))})
    act
  where
    inc (BLocal ix ty) = BLocal (ix + 1) ty
    inc b = b

bindAll :: Elab sig m => N.Telescope -> [Name] -> m a -> m a
bindAll T.Empty _ act = act
bindAll (T.Bind ty tele) (name:names) act = bindLocal name ty (bindAll tele names act)
bindAll _ [] act = do
  report TooManyParams
  act

addDecls :: Elab sig m => [DeclarationAst] -> m a -> m a
addDecls [] act = act
addDecls (decl@(DeclAst (Datatype _ _ constrs) _):decls) act = do
  state <- get
  put (state
    { unDecls =
      union
        (insert (unId decl) (PDDecl decl) (unDecls state))
        (fromList (zip (map unCId constrs) (map PDConstr constrs))) })
  local
    (\ctx -> ctx
      { unBindings =
        union
          (insert (unDeclName decl) (BGlobal (unId decl)) (unBindings ctx))
          (fromList (zip (map unConstrName constrs) (map (BGlobal . unCId) constrs))) })
    (addDecls decls act)
addDecls (decl:decls) act = do
  state <- get
  put (state { unDecls = insert (unId decl) (PDDecl decl) (unDecls state) })
  local
    (\ctx -> ctx { unBindings = insert (unDeclName decl) (BGlobal (unId decl)) (unBindings ctx) })
    (addDecls decls act)

getDecl :: Elab sig m => Id -> m Predeclaration
getDecl did = do
  decls <- unDecls <$> get
  pure (decls ! did)

freshTypeUV :: Elab sig m => m N.Term
freshTypeUV = do
  state <- get
  put (state
    { unNextUV = unNextUV state + 1
    , unTypeUVs = insert (unNextUV state) Nothing (unTypeUVs state) })
  pure (N.UniVar (unNextUV state))

freshStageUV :: Elab sig m => m Stage
freshStageUV = do
  state <- get
  put (state
    { unNextUV = unNextUV state + 1
    , unStageUVs = insert (unNextUV state) Nothing (unStageUVs state) })
  pure (UniVar (unNextUV state))

report :: Elab sig m => Error -> m ()
report _ = pure ()