module Search where

import Data.Maybe
import Syntax.Semantic
import Control.Effect.NonDet(NonDet, Alternative, empty, (<|>), oneOf)
import Control.Effect.State(State, get, put, modify)
import Control.Carrier.NonDet.Church hiding(Empty)
import Control.Carrier.State.Strict
import Control.Carrier.Reader
import Control.Effect.Throw
import Control.Algebra(Has, run)
import Normalization
import Unification hiding(Substitution, unUVEqs)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Syntax.Common(Global(..))
import Numeric.Natural
import Data.Sequence hiding(empty)
import Extra
import Debug.Trace
import Control.Applicative
import Shower
import Prelude hiding(length, zip, concatMap, concat, filter, null, head, tail)
import Prelude qualified as Pre
import Data.Bifunctor
import Data.Foldable(foldl', toList)
import PrettyPrint hiding(unUVEqs)
import Data.Set qualified as Set
import Data.Tree
import Syntax.Core qualified as C
import Data.Maybe

data SearchState = SearchState
  { unNextUV :: Natural
  , unNextId :: Natural
  , unTree :: Map.Map Natural (SearchNode, Natural) }

type Search sig m =
  ( Alternative m
  , Has NonDet sig m
  , Norm sig m
  , Has (Reader Natural) sig m
  , Has (State SearchState) sig m )

type Substitution = (Map.Map Global UVSolution, Map.Map Global Global)

withSubst :: Search sig m => Substitution -> m a -> m a
withSubst (subst, eqs) =
  local
    (\ctx -> ctx
      { unTypeUVs = subst <> unTypeUVs ctx
      , unUVEqs = eqs <> unUVEqs ctx})

concatSubsts Empty = mempty
concatSubsts ((ts, eqs) :<| substs) =
  let (ts', eqs') = concatSubsts substs
  in (ts <> ts', eqs <> eqs')

unionSubsts (ts1, eqs1) (ts2, eqs2) = (ts1 <> ts2, eqs1 <> eqs2)

prove :: forall sig m. Search sig m => Seq Term -> Term -> m Substitution
prove ctx goal@(Neutral p _) =
  (do
    def <- oneOf ctx
    snd <$> search ctx goal def) <|>
  (do
    p <- force p
    case p of
      Just p -> prove ctx p
      Nothing -> failSearch)
prove ctx (Rigid (ConjType p q)) = do
  subst <- prove ctx p
  withSubst subst (prove ctx q)
prove ctx (Rigid (DisjType p q)) =
  prove ctx p <|> prove ctx q
-- prove ctx (Rigid (SomeType (MetaFunIntro p))) = trace "PROVE 4" do
--   uv <- freshUV
--   vP <- appClosure p uv
--   prove ctx vP
prove ctx (Rigid (ImplType p q)) =
  prove (p <| ctx) q
prove ctx (MetaFunType _ _ p) = do
  vP <- evalClosure p
  prove ctx vP
-- prove ctx (Rigid (AllType (MetaFunIntro p))) = trace "PROVE 7" do
--   vP <- evalClosure p
--   prove ctx vP
prove ctx (Rigid (PropIdType x y)) = do
  r <- unifyRS x y
  case r of
    Just (Subst ts eqs) -> pure (ts, eqs)
    Nothing -> failSearch
prove _ goal = failSearch

search :: Search sig m => Seq Term -> Term -> Term -> m (Natural, Substitution)
search ctx g@(MetaFunElims gHead gArgs) d@(MetaFunElims dHead dArgs)
  | length dArgs == length gArgs
  = do
    -- normCtx <- ask
    -- let !_ = tracePrettyS "CTX" (unTypeUVs normCtx)
    -- let !_ = tracePrettyS "DARGS" (dHead <| dArgs)
    -- let !_ = tracePrettyS "GARGS" (dHead <| gArgs)
    substs <-
      traverse
        (\(dArg, gArg) -> unifyRS gArg dArg)
        (zip dArgs gArgs)
    -- let !_ = tracePrettyS "DEF" d
    -- let !_ = tracePrettyS "GOAL" g
    substs <- ((<| substs) <$> unifyRS gHead dHead)
    -- let !_ = tracePrettyS "SUBSTS" substs
    tid <- case head substs of
      Just _ -> do
        cD <- zonk d
        tid <- addNode (Atom cD)
        case allJustOrNothing (tail substs) of
          Just _ -> pure tid
          Nothing -> withId tid (addNode Fail) *> pure 0
      Nothing -> pure 0
    case allJustOrNothing substs of
      Just substs ->
        pure (tid, concatSubsts (fmap (\(Subst ts eqs) -> (ts, eqs)) substs))
      Nothing -> failSearch
-- search ctx goal (Rigid (AllType (MetaFunIntro p))) = trace "SEARCH 2" do
--   uv <- freshUV
--   vP <- appClosure p uv
--   search ctx goal vP
search ctx goal (MetaFunType _ _ p) = do
  uv <- freshUV
  vP <- appClosure p uv
  search ctx goal vP
search ctx goal (Rigid (ImplType p q)) = do
  (tid, qSubst) <- search ctx goal q
  pSubst <- withId tid . withSubst qSubst $ prove ctx p
  pure (tid, qSubst `unionSubsts` pSubst)
search ctx goal (Neutral p _) = do
  p <- force p
  case p of
    Just p -> search ctx goal p
    Nothing -> failSearch
search _ g d = failSearch

freshUV :: Search sig m => m Term
freshUV = do
  state <- get
  put (state { unNextUV = unNextUV state + 1 })
  pure
    (Neutral (uvRedex . LVGlobal $ unNextUV state) .
    flip UniVar (Just (Rigid Dummy)) .
    LVGlobal $
    unNextUV state)

freshId :: Search sig m => m Natural
freshId = do
  tid <- unNextId <$> get
  modify (\st -> st { unNextId = unNextId st + 1 })
  pure tid

addNode :: Search sig m => SearchNode -> m Natural
addNode node = do
  tid <- freshId
  tid' <- ask
  modify (\st -> st
    { unTree =
        Map.insert
          tid
          (node, tid')
          (unTree st) })
  pure tid

withId :: Search sig m => Natural -> m a -> m a
withId tid = local (const tid)

isAtomic :: Term -> Bool
isAtomic (MetaFunElims _ _) = True
isAtomic _ = False

proveDet ::
  Norm sig m =>
  Seq Term ->
  Term ->
  Natural ->
  m (Tree SearchNode, Natural, Maybe (Seq Substitution))
proveDet ctx goal uv = do
  cGoal <- readback goal
  (ss, substs) <-
    runReader (0 :: Natural) .
    runState (SearchState uv 1 mempty) .
    runNonDetA $
    prove ctx goal
  let trees = makeTrees 0 (unTree ss)
  (Node (Atom cGoal) trees, unNextUV ss, ) <$>
    if null substs then
      pure Nothing
    else
      pure (Just substs)

data SearchNode
  = Atom C.Term
  | Fail

failSearch :: Search sig m => m a
failSearch = freshId >>= \tid -> withId tid (addNode Fail) *> empty

makeTrees :: Natural -> Map.Map Natural (SearchNode, Natural) -> [Tree SearchNode]
makeTrees tid m =
  let m' = Map.filter (\(_, tid') -> tid == tid') m
  in
    fmap
      (\(tid', (tree, cs)) -> Node tree (makeTrees tid' m))
      (Map.toList m')
