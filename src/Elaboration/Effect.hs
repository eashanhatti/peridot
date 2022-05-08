module Elaboration.Effect where

import Control.Effect.State(State, get, put)
import Control.Carrier.State.Strict
import Control.Effect.Reader(Reader, ask, local)
import Control.Carrier.Reader
import Control.Effect.Throw(Throw)
import Control.Carrier.Throw.Either
import Control.Effect.NonDet(NonDet)
import Control.Algebra(Has, Algebra)
import Data.Set(Set, singleton)
import Data.Set qualified as Set
import Data.Map(Map, insert, union, fromList, lookup)
import Data.Map qualified as Map
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Surface
import Syntax.Common hiding(unId)
import Data.Some
import Data.Maybe(isJust, fromMaybe, fromJust)
import Data.Dependent.HashMap qualified as DMap
import Data.Dependent.HashMap(DHashMap)
import Data.Functor.Identity
import Data.GADT.Compare
import Data.Type.Equality
import Data.Hashable
import GHC.Generics hiding (Constructor, C)
import Normalization hiding (eval, unTypeUVs, unRepUVs, unUVEqs, unVCUVs, readback', readback', zonk)
import Normalization qualified as Norm
import Unification qualified as Uni
import Numeric.Natural
import Data.Foldable(toList, foldl', foldlM)
import Prelude hiding(lookup, zip, filter)
import Prelude qualified as Pre
import GHC.Stack
import Extra
import Text.Megaparsec(SourcePos)
import Debug.Trace
import Data.Sequence
import Control.Monad.Fix

-- Contains query state *and* general global state
data QueryState = QueryState
  { unMemoTable :: DHashMap Key Identity
  , unPredecls :: Map Id (AllState, Predeclaration)
  , unNextUV :: Global
  , unTypeUVs :: Map Global (Maybe N.Term)
  , unUnivUVs :: Map Global (Maybe N.Universe)
  -- , unVCUVs :: Map Global (Maybe N.ValueCategory)
  , unUVEqs :: Map Global Global
  , unErrors :: Seq (SourcePos, Error) }

instance Show QueryState where
  show (QueryState _ _ _ tuvs suvs {-vcuvs-} eqs errs) = show (tuvs, suvs, {-vcuvs,-} eqs{-, errs-})

data Error
  = TooManyParams
  | WrongAppArity Natural Natural
  | FailedUnify N.Term N.Term
  | UnboundVariable Name
  | ExpectedCFunType N.Term
  | FailedProve N.Term
  | AmbiguousProve N.Term (Seq (Map Global N.Term))
  deriving (Show)

type Query sig m = Has (State QueryState) sig m

data AllState = AllState ElabState ElabContext NormContext
  deriving (Show)

type C m a =
  ReaderC
    NormContext
      (ReaderC ElabContext (StateC ElabState m))
    a

restore :: Query sig m => AllState -> C m a -> m a
restore (AllState es ec nc) act =
  evalState es $
  runReader ec $
  runReader nc $
  act

data Key a where
  CheckDecl :: Id -> Key C.Declaration
  DeclType :: Id -> Key (C.Term, N.Term)


instance GEq Key where
  geq (CheckDecl _) (CheckDecl _) = Just Refl
  geq (DeclType _) (DeclType _) = Just Refl
  geq _ _ = Nothing

instance Hashable (Some Key) where
  hashWithSalt salt (Some (CheckDecl did)) = salt `hashWithSalt` did
  hashWithSalt salt (Some (DeclType did)) = salt `hashWithSalt` (did + 1000000)

memo :: Query sig m => Key a -> StateC QueryState Identity a -> m a
memo key act = do
  state <- get
  case DMap.lookup key (unMemoTable state) of
    Just (Identity result) -> pure result
    Nothing -> do
      let (state', result) = run . runState state $ act
      put (state' { unMemoTable = DMap.insert key (Identity result) (unMemoTable state) })
      pure result

data Binding = BLocal Index N.Term | BGlobal Id
  deriving (Eq, Show)

instance Ord Binding where
  compare (BLocal ix1 _) (BLocal ix2 _) = compare ix1 ix2
  compare (BGlobal did1) (BGlobal did2) = compare did1 did2
  compare (BLocal _ _) (BGlobal _) = LT
  compare (BGlobal _) (BLocal _ _) = GT

data ElabContext = ElabContext
  { unBindings :: Map Name Binding
  , unSourcePos :: SourcePos }
  deriving (Show)

data Predeclaration = PDDecl DeclarationAst | PDConstr Universe ConstructorAst
  deriving (Show)

unPDDeclId :: Predeclaration -> Id
unPDDeclId (PDDecl (DeclAst _ did)) = did
unPDDeclId (PDConstr _ (ConstrAst _ did _)) = did
unPDDeclId (PDDecl (SourcePos (DeclAst _ did) _)) = did
unPDDeclId (PDConstr _ (SourcePos (ConstrAst _ did _) _)) = did

convertUniv :: Universe -> N.Universe
convertUniv Obj = N.Obj
convertUniv Meta = N.Meta
convertUniv Prop = N.Prop

-- Move unification stuff to `QueryState`, but I'll leave this around just in case
data ElabState = ElabState
  {  }
  deriving (Show)

type Elab sig m =
  ( MonadFix m
  , Has (Reader ElabContext) sig m
  , Has (State ElabState) sig m
  , Norm sig m
  , Query sig m )

unify :: Elab sig m => N.Term -> N.Term -> m ()
unify term1 term2 = do
  subst <- Uni.unify term1 term2
  case subst of
    Just (Uni.Subst ts ss {-vcs-} eqs) -> do
      state <- get
      put (state
        { unTypeUVs = fmap Just ts <> unTypeUVs state
        , unUnivUVs = fmap Just ss <> unUnivUVs state
        -- , unVCUVs = fmap Just vcs <> unVCUVs state
        , unUVEqs = eqs <> unUVEqs state })
    Nothing -> report (FailedUnify term1 term2)

convertible :: Elab sig m => N.Term -> N.Term -> m Bool
convertible term1 term2 = isJust <$> Uni.unify term1 term2

putTypeUVSols :: Elab sig m => Map Global N.Term -> m ()
putTypeUVSols sols = do
  state <- get
  put (state { unTypeUVs = fmap Just sols <> unTypeUVs state })

bindLocal :: Elab sig m => Name -> N.Term -> m a -> m a
bindLocal name ty act =
  local (\ctx -> ctx { unBindings = insert name (BLocal (Index 0) ty) (fmap inc (unBindings ctx)) }) .
  bind $
  act
  where
    inc (BLocal ix ty) = BLocal (ix + 1) ty
    inc b = b

bindLocalMany :: Elab sig m => Seq (Name, N.Term) -> m a -> m a
bindLocalMany Empty = id
bindLocalMany ((name, ty) :<| ls) = bindLocal name ty . bindLocalMany ls

withPos :: Elab sig m => SourcePos -> m a -> m a
withPos pos = local (\ctx -> ctx { unSourcePos = pos })

withDecls :: forall sig m a. Elab sig m => Seq DeclarationAst -> m a -> m a
withDecls decls act = do
  elabState <- get
  elabContext <- ask
  normContext <- ask
  let
    bindings' = toBindings decls `union` unBindings elabContext
    allState = AllState elabState (elabContext { unBindings = bindings' }) normContext

    toBindings :: Seq DeclarationAst -> Map Name Binding
    toBindings Empty = mempty
    toBindings (decl@(viewConstrs -> Just (_, constrs)) :<| decls) = 
      foldl'
        (\m (n, b) -> insert n b m)
        (toBindings decls)
        ((unDeclName decl, BGlobal (unId decl)) <| zip (fmap unConstrName constrs) (fmap (BGlobal . unCId) constrs))
    toBindings (decl :<| decls) =
      insert (unDeclName decl) (BGlobal (unId decl)) (toBindings decls)

    go :: Elab sig m => Seq DeclarationAst -> m a
    go Empty = act
    go (decl@(viewConstrs -> Just (univ, constrs)) :<| decls) = do
      state <- get
      put (state
        { unPredecls =
            union
              (insert (unId decl) (allState, PDDecl decl) (unPredecls state))
              (foldl' (\acc c -> Map.insert (unCId c) (allState, PDConstr univ c) acc) mempty constrs) })
      go decls
    go (decl :<| decls) = do
      state <- get
      put (state { unPredecls = insert (unId decl) (allState, PDDecl decl) (unPredecls state) })
      go decls
  local (\ctx -> ctx { unBindings = bindings' }) (go decls)

lookupBinding :: Elab sig m => Name -> m (Maybe Binding)
lookupBinding name = do
  bindings <- unBindings <$> ask
  pure (Map.lookup name bindings)

withDecl :: Query sig m => Id -> (Predeclaration -> C m a) -> m a
withDecl did act = do
  (as, decl) <- (! did) . unPredecls <$> get
  restore as (act decl)

freshTypeUV :: Elab sig m => m N.Term
freshTypeUV = do
  state <- get
  put (state
    { unTypeUVs = insert (unNextUV state) Nothing (unTypeUVs state)
    , unNextUV = unNextUV state + 1 })
  pure (N.Neutral (uvRedex (unNextUV state)) (N.UniVar (unNextUV state)))

-- freshVCUV :: Elab sig m => m N.ValueCategory
-- freshVCUV = do
--   state <- get
--   put (state
--     { unVCUVs = insert (unNextUV state) Nothing (unVCUVs state)
--     , unNextUV = unNextUV state + 1 })
--   pure (N.VCUniVar (unNextUV state))

-- freshUniverseUV :: Elab sig m => m Universe
-- freshUniverseUV = do
--   state <- get
--   put (state
--     { unUnivUVs = insert (unNextUV state) Nothing (unUnivUVs state)
--     , unNextUV = unNextUV state + 1 })
--   pure (SUniVar (unNextUV state))

report :: Elab sig m => Error -> m ()
report err = do
  state <- get
  pos <- unSourcePos <$> ask
  put (state { unErrors = (pos, err) <| unErrors state })

errorTerm :: Elab sig m => Error -> m (C.Term, N.Term)
errorTerm err = do
  report err
  pure (C.Rigid C.ElabError, N.Rigid N.ElabError)

errorDecl :: Elab sig m => Error -> m C.Declaration
errorDecl err = do
  report err
  pure C.DElabError

eval :: forall sig m. Elab sig m => C.Term -> m N.Term
eval term = do
  memoTable <- unMemoTable <$> get
  let
    f = \case
      CheckDecl _ DMap.:=> _ -> True
      _ -> False
    decls :: [C.Declaration]
    decls =
      map (\case CheckDecl _ DMap.:=> Identity gl -> gl) .
      Pre.filter f .
      DMap.toList $
      memoTable
  ctx@(unEnv -> N.Env locals globals) <- ask
  -- let vDefs = foldl' (\acc def -> Map.insert (C.unId def) (N.Env locals (vDefs <> globals), Norm.definition def) acc) mempty decls
  rec
    (vDefs :: Map.Map Id N.Term) <- (\f -> foldlM f mempty decls) \acc decl -> do
      vDecl <- local
        (\ctx -> ctx { unEnv = N.Env locals (vDefs <> globals) })
        (Norm.eval (Norm.definition decl))
      pure (Map.insert (C.unId decl) vDecl acc)
  local (\ctx -> ctx { unEnv = N.Env locals (globals <> vDefs) }) (Norm.eval term)

readback' :: Elab sig m => Bool -> N.Term -> m C.Term
readback' unf term = do
  typeUVs <- unTypeUVs <$> get
  eqs <- unUVEqs <$> get
  local (\ctx -> ctx
    { Norm.unTypeUVs = fmap fromJust . Map.filter isJust $ typeUVs
    , Norm.unUVEqs = eqs })
    (Norm.readback' unf term)

zonk :: Elab sig m => N.Term -> m C.Term
zonk = readback' True

readback :: Elab sig m => N.Term -> m C.Term
readback = readback' False
