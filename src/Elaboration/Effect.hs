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
import Syntax.Common hiding(unId, Universe(..))
import Data.Some
import Data.Maybe
import Data.Dependent.HashMap qualified as DMap
import Data.Dependent.HashMap(DHashMap)
import Data.Functor.Identity
import Data.GADT.Compare
import Data.GADT.Show
import Data.Type.Equality qualified as Equal
import Data.Hashable
import GHC.Generics hiding (Constructor, C)
import Normalization hiding(eval, unTypeUVs, unRepUVs, unUVEqs, unVCUVs, readback', readback, zonk)
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
import Data.Bifunctor
import Search qualified
import Data.Tree

data QueryContext = QueryContext
  { unCurQuery :: Maybe (Some Key) }

-- Contains query state *and* general global state
data QueryState = QueryState
  { unMemoTable :: DHashMap Key Identity
  , unPredecls :: Map Id (AllState, Predeclaration)
  , unNextUV :: Natural
  , unTypeUVs :: Map Global (Maybe UVSolution)
  , unUVEqs :: Map Global Global
  , unErrors :: Seq (SourcePos, Error)
  , unDepGraph :: Map (Some Key) (Set (Some Key))
  , unLogvarNames :: Map Global Name
  , unLogvars :: Set Id
  , unOutputs :: Seq (FilePath, N.Term)
  , unNextLogUV :: Natural
  , unSearchTrees :: Seq (Tree Search.SearchNode) }

instance Show QueryState where
  show (QueryState _ _ _ tuvs eqs errs _ _ _ _ _ _) =
    show (tuvs, eqs, errs)

data Error
  = TooManyParams
  | TooManyArgs C.Term
  | WrongAppArity Natural Natural
  | FailedUnify C.Term C.Term
  | UnboundVariable Name
  | ExpectedRecordType C.Term
  | MissingField Name
  | FailedProve C.Term N.Term (Seq N.Term)
  | AmbiguousProve C.Term (Seq (Map.Map Global UVSolution, Map.Map Global Global))
  | InferredFunType C.Term
  | ExpectedFunType C.Term
  | CannotInfer TermAst
  | AmbiguousCallUniv
  deriving (Show)

type Query sig m = 
  ( Has (State QueryState) sig m
  , Has (Reader QueryContext) sig m )

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
  CheckDecl :: Id -> Key C.Term
  DeclType :: Id -> Key (C.Term, N.Universe) -- sig, univ

instance Show (Key a) where
  show (CheckDecl did) = "(CheckDecl " ++ show did ++ ")"
  show (DeclType did) = "(DeclType " ++ show did ++ ")"

instance GShow Key where
  gshowsPrec = showsPrec

instance GCompare Key where
  gcompare (CheckDecl did1) (CheckDecl did2) =
    case compare did1 did2 of
      LT -> GLT
      GT -> GGT
      EQ -> GEQ
  gcompare (CheckDecl _) (DeclType _) = GLT
  gcompare (DeclType _) (CheckDecl _) = GGT
  gcompare (DeclType did1) (DeclType did2) =
    case compare did1 did2 of
      LT -> GLT
      GT -> GGT
      EQ -> GEQ

instance GEq Key where
  geq (CheckDecl did1) (CheckDecl did2) =
    if did1 == did2 then
      Just Equal.Refl
    else
      Nothing
  geq (DeclType did1) (DeclType did2) =
    if did1 == did2 then
      Just Equal.Refl
    else
      Nothing
  geq _ _ = Nothing

instance Hashable (Some Key) where
  hashWithSalt salt (Some (CheckDecl did)) = salt `hashWithSalt` did
  hashWithSalt salt (Some (DeclType did)) = salt `hashWithSalt` (did + 1000000)

type QC a = ReaderC QueryContext (StateC QueryState Identity) a

memo :: Query sig m => Key a -> QC a -> m a
memo key act = do
  modify (\st -> st
    { unDepGraph =
        case Map.lookup (Some key) (unDepGraph st) of
          Just _ -> unDepGraph st
          Nothing -> Map.insert (Some key) mempty (unDepGraph st) })
  state <- get
  r <- case DMap.lookup key (unMemoTable state) of
    Just (Identity result) -> pure result
    Nothing -> do
      let
        (state', result) =
          run .
          runState state .
          runReader (QueryContext (Just (Some key))) $
          act
      put (state'
        { unMemoTable = DMap.insert key (Identity result) (unMemoTable state) })
      pure result
  cq <- unCurQuery <$> ask
  modify (\st -> st
    { unDepGraph =
        case cq of
          Just cq ->
            let set = Set.insert (Some key) (fromJust (Map.lookup cq (unDepGraph st)))
            in Map.insert cq set (unDepGraph st)
          Nothing -> unDepGraph st })
  pure r

data Binding = BLocal Index N.Term | BGlobal Id
  deriving (Eq, Show)

instance Ord Binding where
  compare (BLocal ix1 _) (BLocal ix2 _) = compare ix1 ix2
  compare (BGlobal did1) (BGlobal did2) = compare did1 did2
  compare (BLocal _ _) (BGlobal _) = LT
  compare (BGlobal _) (BLocal _ _) = GT

data ElabContext = ElabContext
  { unBindings :: Map Name Binding
  , unSourcePos :: SourcePos
  , unAxioms :: Set Id
  , unIsType :: Bool }
  deriving (Show)

data Predeclaration = PDDecl DeclarationAst
  deriving (Show)

unPDDeclName :: Predeclaration -> Name
unPDDeclName (PDDecl decl) = unDeclName decl

unPDDeclId :: Predeclaration -> Id
unPDDeclId (PDDecl (DeclAst _ did)) = did
unPDDeclId (PDDecl (SourcePos (DeclAst _ did) _)) = did

convertUniv :: Universe -> N.Universe
convertUniv Obj = N.Obj
convertUniv Meta = N.Meta

-- Moved unification stuff to `QueryState`, but I'll leave this around just in case
data ElabState = ElabState
  {  }
  deriving (Show)

type Elab sig m =
  ( MonadFix m
  , Has (Reader ElabContext) sig m
  , Has (State ElabState) sig m
  , Norm sig m
  , Query sig m )

asType :: Elab sig m => m a -> m a
asType = local (\ctx -> ctx { unIsType = True })

unify :: Elab sig m => C.Term -> N.Term -> N.Term -> m C.Term
unify e term1 term2 = do
  vDefs <- allDefs
  typeUVs <- unTypeUVs <$> get
  eqs <- unUVEqs <$> get
  ctx@(unEnv -> N.Env locals globals) <- ask
  r <-
    local
      (\ctx -> ctx
        { unEnv = N.Env locals (globals <> vDefs)
        , Norm.unTypeUVs = fmap fromJust . Map.filter isJust $ typeUVs
        , Norm.unUVEqs = eqs
        })
      (Uni.unify e term1 term2)
  case r of
    Just (Uni.Subst ts eqs, e') -> do
      modify (\st -> st
        { unTypeUVs = fmap Just ts <> unTypeUVs st
        , unUVEqs = eqs <> unUVEqs st })
      pure e'
    Nothing -> do
      cTerm1 <- zonk term1
      cTerm2 <- zonk term2
      report (FailedUnify cTerm1 cTerm2)
      pure e

unifyR :: Elab sig m => N.Term -> N.Term -> m ()
unifyR term1 term2 = do
  vDefs <- allDefs
  typeUVs <- unTypeUVs <$> get
  eqs <- unUVEqs <$> get
  ctx@(unEnv -> N.Env locals globals) <- ask
  subst <-
    local
      (\ctx -> ctx
        { unEnv = N.Env locals (globals <> vDefs)
        , Norm.unTypeUVs = fmap fromJust . Map.filter isJust $ typeUVs
        , Norm.unUVEqs = eqs
        })
      (Uni.unifyR term1 term2)
  case subst of
    Just (Uni.Subst ts eqs) ->
      modify (\st -> st
        { unTypeUVs = fmap Just ts <> unTypeUVs st
        , unUVEqs = eqs <> unUVEqs st })
    Nothing -> do
      cTerm1 <- zonk term1
      cTerm2 <- zonk term2
      report (FailedUnify cTerm1 cTerm2)

convertible :: Elab sig m => N.Term -> N.Term -> m Bool
convertible term1 term2 = do
  vDefs <- allDefs
  typeUVs <- unTypeUVs <$> get
  eqs <- unUVEqs <$> get
  ctx@(unEnv -> N.Env locals globals) <- ask
  local
    (\ctx -> ctx
      { unEnv = N.Env locals (globals <> vDefs)
      , Norm.unTypeUVs = fmap fromJust . Map.filter isJust $ typeUVs
      , Norm.unUVEqs = eqs
      })
    (isJust <$> Uni.unifyR term1 term2)

convertibleO :: Elab sig m => N.Term -> N.Term -> m Bool
convertibleO term1 term2 = do
  vDefs <- allDefs
  typeUVs <- unTypeUVs <$> get
  eqs <- unUVEqs <$> get
  ctx@(unEnv -> N.Env locals globals) <- ask
  subst <-
    local
      (\ctx -> ctx
        { unEnv = N.Env locals (globals <> vDefs)
        , Norm.unTypeUVs = fmap fromJust . Map.filter isJust $ typeUVs
        , Norm.unUVEqs = eqs
        })
      (Uni.unifyR term1 term2)
  case subst of
    Just (Uni.Subst ts eqs) -> do
      modify (\st -> st
        { unTypeUVs = fmap Just ts <> unTypeUVs st
        , unUVEqs = eqs <> unUVEqs st })
      pure True
    Nothing -> do
      cTerm1 <- zonk term1
      cTerm2 <- zonk term2
      report (FailedUnify cTerm1 cTerm2)
      pure False

putTypeUVSols :: Elab sig m => Map Global UVSolution -> m ()
putTypeUVSols sols =
  modify (\st -> st { unTypeUVs = fmap Just sols <> unTypeUVs st })

putUVEqs :: Elab sig m => Map Global Global -> m ()
putUVEqs eqs =
  modify (\st -> st { unUVEqs = eqs <> unUVEqs st })

bindLocal :: Elab sig m => Name -> N.Term -> m a -> m a
bindLocal name ty act =
  local (\ctx ->
    ctx { unBindings =
      case name of
        Unbound -> fmap inc (unBindings ctx)
        _ -> insert name (BLocal (Index 0) ty) (fmap inc (unBindings ctx)) }) .
  bind $
  act
  where
    inc (BLocal ix ty) = BLocal (ix + 1) ty
    inc b = b

noLocals :: Elab sig m => m a -> m a
noLocals =
  local (\ctx -> ctx
    { unBindings =
      flip Map.filter
        (unBindings ctx)
        \case
          BGlobal _ -> True
          BLocal _ _ -> False })

defineLocal :: Elab sig m => Name -> N.Term -> N.Term -> m a -> m a
defineLocal name ty def act =
  local (\ctx ->
    ctx { unBindings =
      case name of
        Unbound -> fmap inc (unBindings ctx)
        _ -> insert name (BLocal (Index 0) ty) (fmap inc (unBindings ctx)) }) .
  define def $
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
    bindings' = toBindings decls <> unBindings elabContext
    axioms' = toAxioms decls <> unAxioms elabContext
    allState =
      AllState
        elabState
        (elabContext { unBindings = bindings', unAxioms = axioms' })
        normContext

    toAxioms :: Seq DeclarationAst -> Set Id
    toAxioms Empty = mempty
    toAxioms (decl :<| decls) =
      case stripSourcePos decl of
        Axiom _ _ -> Set.insert (unId decl) (toAxioms decls)
        _ -> toAxioms decls

    toBindings :: Seq DeclarationAst -> Map Name Binding
    toBindings Empty = mempty
    toBindings (decl :<| decls) =
      insert (unDeclName decl) (BGlobal (unId decl)) (toBindings decls)

    go :: Elab sig m => Seq DeclarationAst -> m a
    go Empty = act
    go (decl :<| decls) = do
      state <- get
      put (state
        { unPredecls = insert (unId decl) (allState, PDDecl decl) (unPredecls state) })
      go decls
  local (\ctx -> ctx { unBindings = bindings', unAxioms = axioms' }) (go decls)

lookupBinding :: Elab sig m => Name -> m (Maybe Binding)
lookupBinding name = do
  bindings <- unBindings <$> ask
  pure (Map.lookup name bindings)

withDecl :: Query sig m => Id -> (Predeclaration -> C m a) -> m a
withDecl did act = do
  (as, decl) <- (! did) . unPredecls <$> get
  restore as (act decl)

freshBareTypeUV :: Elab sig m => m Global
freshBareTypeUV = do
  state <- get
  put (state
    { unTypeUVs = insert (UVGlobal (unNextUV state)) Nothing (unTypeUVs state)
    , unNextUV = unNextUV state + 1 })
  pure (UVGlobal (unNextUV state))

freshTypeUV :: Elab sig m => m N.Term
freshTypeUV = do
  state <- get
  put (state
    { unTypeUVs = insert (UVGlobal (unNextUV state)) Nothing (unTypeUVs state)
    , unNextUV = unNextUV state + 1 })
  pure
    (N.Neutral
      (uvRedex (UVGlobal (unNextUV state)))
      (N.UniVar (UVGlobal (unNextUV state))))

scopeUVState :: Elab sig m => m a -> m a
scopeUVState act = do
  state <- get
  r <- act
  modify (\st -> st
    { unNextUV = unNextUV state
    , unTypeUVs = unTypeUVs state
    , unUVEqs = unUVEqs state })
  pure r

report :: Elab sig m => Error -> m ()
report err = do
  state <- get
  pos <- unSourcePos <$> ask
  put (state { unErrors = (pos, err) <| unErrors state })

errorTerm :: Elab sig m => Error -> m (C.Term, N.Term)
errorTerm err = do
  report err
  pure (C.Rigid C.ElabError, N.Rigid N.ElabError)

eval :: forall sig m. Elab sig m => C.Term -> m N.Term
eval term = do
  vDefs <- allDefs
  ctx@(unEnv -> N.Env locals globals) <- ask
  local (\ctx -> ctx { unEnv = N.Env locals (globals <> vDefs) }) (Norm.eval term)

allDefs :: Elab sig m => m (Map Id N.Term)
allDefs = do
  memoTable <- unMemoTable <$> get
  let
    f = \case
      CheckDecl _ DMap.:=> _ -> True
      _ -> False
    decls :: [(Id, C.Term)]
    decls =
      map (\case CheckDecl did DMap.:=> Identity def -> (did, def)) .
      Pre.filter f .
      DMap.toList $
      memoTable
  ctx@(unEnv -> N.Env locals globals) <- ask
  rec
    (vDefs :: Map.Map Id N.Term) <- (\f -> foldlM f mempty decls) \acc (did, decl) -> do
      vDecl <- local
        (\ctx -> ctx { unEnv = N.Env locals (vDefs <> globals) })
        (Norm.eval decl)
      pure (Map.insert did vDecl acc)
  pure vDefs

readback' :: Elab sig m => ReadbackDepth -> N.Term -> m C.Term
readback' unf term = do
  typeUVs <- unTypeUVs <$> get
  eqs <- unUVEqs <$> get
  local (\ctx -> ctx
    { Norm.unTypeUVs = justs typeUVs
    , Norm.unUVEqs = eqs })
    (Norm.readback' unf term)

zonk :: Elab sig m => N.Term -> m C.Term
zonk = readback' Zonk

readback :: Elab sig m => N.Term -> m C.Term
readback = readback' None

proveDet ::
  Elab sig m =>
  Seq N.Term ->
  N.Term ->
  m (Tree Search.SearchNode, Maybe (Seq Search.Substitution))
proveDet ctx goal = do
  nextUV <- unNextLogUV <$> get
  typeUVs <- unTypeUVs <$> get
  eqs <- unUVEqs <$> get
  (tree, nextUV', r) <-
    local (\ctx -> ctx
      { Norm.unTypeUVs = justs typeUVs
      , Norm.unUVEqs = eqs })
      (Search.proveDet ctx goal nextUV)
  modify (\st -> st { unNextUV = nextUV' })
  pure (tree, r)
