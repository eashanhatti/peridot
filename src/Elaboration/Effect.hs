module Elaboration.Effect where

import Control.Effect.State(State, get, put)
import Control.Effect.Reader(Reader, ask, local)
import Control.Effect.Throw(Throw)
import Control.Effect.NonDet(NonDet)
import Control.Algebra(Has)
import Data.Set(Set, singleton)
import Data.Set qualified as Set
import Data.Map(Map, (!), insert, union, fromList, lookup)
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Surface
import Syntax.Extra hiding(unId)
import Data.Some
import Data.Maybe(isJust)
import Data.Dependent.HashMap qualified as DMap
import Data.Dependent.HashMap(DHashMap)
import Data.Functor.Identity
import Data.GADT.Compare
import Data.Type.Equality
import Data.Hashable
import GHC.Generics hiding (Constructor)
import Normalization
import Unification qualified as U
import Numeric.Natural
import Data.Foldable(toList, foldl')
import Prelude hiding(lookup)

data QueryState = QueryState
  { unMemoTable :: DHashMap Key Identity }

data Error
  = TooManyParams
  | WrongAppArity Natural Natural
  | FailedUnify N.Term N.Term

type Query sig m = Has (State QueryState) sig m

data Key a where
  CheckDecl :: Predeclaration -> Key C.Declaration
  DeclType :: Id -> Key C.Term

instance GEq Key where
  geq (CheckDecl _) (CheckDecl _) = Just Refl
  geq (DeclType _) (DeclType _) = Just Refl
  geq _ _ = Nothing

instance Hashable (Some Key) where
  hashWithSalt salt (Some (CheckDecl (PDDecl (DeclAst _ did)))) = salt `hashWithSalt` did
  hashWithSalt salt (Some (CheckDecl (PDConstr (ConstrAst _ did _)))) = salt `hashWithSalt` did
  hashWithSalt salt (Some (DeclType did)) = salt `hashWithSalt` did + 1000000

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
  deriving (Eq)

instance Ord Binding where
  compare (BLocal ix1 _) (BLocal ix2 _) = compare ix1 ix2
  compare (BGlobal did1) (BGlobal did2) = compare did1 did2
  compare (BLocal _ _) (BGlobal _) = LT
  compare (BGlobal _) (BLocal _ _) = GT

data ElabContext = ElabContext
  { unBindings :: Map Name (Set Binding) }

data Predeclaration = PDDecl DeclarationAst | PDConstr ConstructorAst

unPDDeclId :: Predeclaration -> Id
unPDDeclId (PDDecl (DeclAst _ did)) = did
unPDDeclId (PDConstr (ConstrAst _ did _)) = did

data ElabState = ElabState
  { unDecls :: Map Id Predeclaration
  , unNextUV :: Global
  , unTypeUVs :: Map Global (Maybe N.Term)
  , unStageUVs :: Map Global (Maybe Stage)
  , unRepUVs :: Map Global (Maybe RuntimeRep) }

type Elab sig m =
  ( MonadFail m
  , Has (Reader ElabContext) sig m
  , Has (State ElabState) sig m
  , Has (Throw ()) sig m
  , Has NonDet sig m
  , Norm sig m
  , Query sig m )

unify :: Elab sig m => N.Term -> N.Term -> m ()
unify term1 term2 = do
  subst <- U.unify term1 term2
  case subst of
    Just (U.Subst ts ss rs) -> do
      state <- get
      put (state
        { unTypeUVs = fmap Just ts <> unTypeUVs state
        , unStageUVs = fmap Just ss <> unStageUVs state
        , unRepUVs = fmap Just rs <> unRepUVs state })
    Nothing -> report (FailedUnify term1 term2)

convertible :: Elab sig m => N.Term -> N.Term -> m Bool
convertible term1 term2 = isJust <$> U.unify term1 term2

overloadBinding k s m = case lookup k m of
  Just s' -> insert k (Set.union s s') m
  Nothing -> insert k s m

bindLocal :: Elab sig m => Name -> N.Term -> m a -> m a
bindLocal name ty act =
  local
    (\ctx -> ctx { unBindings = overloadBinding name (singleton (BLocal (Index 0) ty)) (fmap (Set.map inc) (unBindings ctx)) })
    act
  where
    inc (BLocal ix ty) = BLocal (ix + 1) ty
    inc b = b

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
        foldl'
          (\m (n, b) -> overloadBinding n (singleton b) m)
          (unBindings ctx)
          ((unDeclName decl, BGlobal (unId decl)) : zip (map unConstrName constrs) (map (BGlobal . unCId) constrs)) })
    (addDecls decls act)
addDecls (decl:decls) act = do
  state <- get
  put (state { unDecls = insert (unId decl) (PDDecl decl) (unDecls state) })
  local
    (\ctx -> ctx { unBindings = overloadBinding (unDeclName decl) (singleton (BGlobal (unId decl))) (unBindings ctx) })
    (addDecls decls act)

lookupBinding :: Elab sig m => Name -> m (Maybe Binding)
lookupBinding name = do
  bindings <- unBindings <$> ask
  case fmap toList (lookup name bindings) of
    Nothing -> pure Nothing
    Just [] -> pure Nothing
    Just (b:_) -> pure (Just b)

getDecl :: Elab sig m => Id -> m Predeclaration
getDecl did = do
  decls <- unDecls <$> get
  pure (decls ! did)

freshTypeUV :: Elab sig m => m N.Term
freshTypeUV = do
  state <- get
  put (state
    { unTypeUVs = insert (unNextUV state) Nothing (unTypeUVs state)
    , unNextUV = unNextUV state + 1 })
  pure (N.UniVar (unNextUV state))

freshStageUV :: Elab sig m => m Stage
freshStageUV = undefined

freshRepUV :: Elab sig m => m RuntimeRep
freshRepUV = undefined

report :: Elab sig m => Error -> m ()
report _ = pure ()