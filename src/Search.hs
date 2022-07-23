module Search where

import Data.Maybe
import Syntax.Semantic
import Control.Effect.NonDet(NonDet, Alternative, empty, (<|>), oneOf)
import Control.Effect.State(State, get, put, modify)
import Control.Carrier.NonDet.Church hiding(Empty)
import Control.Carrier.State.Strict
import Control.Carrier.Reader
import Control.Carrier.Error.Either
import Control.Effect.Error
import Control.Algebra(Has, run)
import Normalization
import Unification hiding(Substitution, unUVEqs)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Syntax.Common(Global(..))
import Numeric.Natural
import Data.Sequence hiding(empty)
import Extras
import Debug.Trace
import Control.Applicative
import Control.Monad
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
withSubst subst act = do
  tuvs <- unTypeUVs <$> ask
  eqs <- unUVEqs <$> ask
  (tuvs', eqs') <- concatSubsts (fromList [(tuvs, eqs), subst])
  local
    (\ctx -> ctx
      { unTypeUVs = tuvs'
      , unUVEqs = eqs' })
    act

concatSubsts' :: (Has (Error ()) sig m, Norm sig m) => Seq Substitution -> m Substitution
concatSubsts' Empty = pure mempty
concatSubsts' ((ts, eqs) :<| substs) = do
  (ts', eqs') <- concatSubsts' substs
  overlap <-
    flip filterM (Map.toList ts) \(gl, unTerm -> sol) ->
      case Map.lookup gl ts' of
        Just (unTerm -> sol') -> isNothing <$> unifyRS sol sol'
        Nothing -> pure False
  if fmap fst overlap /= mempty then
    traceShow overlap $ throwError ()
  else
    pure (ts <> ts', eqs <> eqs')

concatSubsts'' :: Search sig m => Seq Substitution -> m (Maybe Substitution)
concatSubsts'' ss = do
  r <- runError @() $ concatSubsts' ss
  case r of
    Right r -> pure (Just r)
    Left _ -> pure Nothing

concatSubsts :: Search sig m => Seq Substitution -> m Substitution
concatSubsts ss = do
  r <- runError @() $ concatSubsts' ss
  case r of
    Right r -> pure r
    Left _ -> empty

unionSubsts subst1 subst2 = concatSubsts (fromList [subst1, subst2])

prove :: forall sig m. Search sig m => Seq Term -> Term -> m Substitution
prove ctx goal@(Neutral p _) =
  (do
    def <- oneOf ctx
    snd <$> search ctx goal def) <|>
  (do
    p <- force p
    case p of
      Just p -> prove ctx p
      Nothing -> empty)
prove ctx (Rigid (ConjType p q)) = do
  subst <- prove ctx p
  withSubst subst (prove ctx q)
prove ctx (Rigid (DisjType p q)) =
  prove ctx p <|> prove ctx q
prove ctx (Rigid (ImplType p q)) =
  prove (p <| ctx) q
prove ctx (MetaFunType _ _ p) = do
  vP <- evalClosure p
  prove ctx vP
prove ctx (Rigid (PropIdType x y)) = do
  r <- unifyRS x y
  case r of
    Just (Subst ts eqs) -> pure (ts, eqs)
    Nothing -> empty
prove _ goal = empty

search :: Search sig m => Seq Term -> Term -> Term -> m (Natural, Substitution)
search ctx g@(MetaFunElims gHead gArgs) d@(MetaFunElims dHead dArgs)
  | length dArgs == length gArgs
  = do
    normCtx <- ask
    let _ = unTypeUVs normCtx
    substs <-
      traverse
        (\(dArg, gArg) -> unifyRS gArg dArg)
        (zip dArgs gArgs)
    -- let !_ = tracePrettyS "DEF" d
    -- let !_ = tracePrettyS "GOAL" g
    substs <- ((<| substs) <$> unifyRS gHead dHead)
    tid <- case head substs of
      Just _ -> do
        cD <- zonk d
        cG <- zonk g
        tid <- addNode (Atom cD cG)
        case allJustOrNothing (tail substs) of
          Just _ -> pure tid
          Nothing -> withId tid (addNode Fail) *> pure 0
      Nothing -> pure 0
    case allJustOrNothing substs of
      Just substs ->
        (tid ,) <$>
          (concatSubsts'' (fmap (\(Subst ts eqs) -> (ts, eqs)) substs) >>= \case
            Just r -> do
              -- let !_ = tracePrettyS "CTX" (unTypeUVs normCtx)
              -- let !_ = tracePrettyS "DARGS" (dHead <| dArgs)
              -- let !_ = tracePrettyS "GARGS" (dHead <| gArgs)
              -- let !_ = tracePrettyS "SUBSTS" substs
              pure r
            Nothing -> withId tid failSearch)
      Nothing -> empty
search ctx goal (MetaFunType _ _ p) = do
  uv <- freshUV
  vP <- appClosure p uv
  define uv (search ctx goal vP)
search ctx goal (Rigid (ImplType p q)) = do
  (tid, qSubst) <- search ctx goal q
  pSubst <- withId tid . withSubst qSubst $ prove ctx p
  (tid ,) <$> qSubst `unionSubsts` pSubst
search ctx goal (Neutral p _) = do
  p <- force p
  case p of
    Just p -> search ctx goal p
    Nothing -> empty
search _ g d = empty

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
  (Node (Atom cGoal (C.Rigid C.Dummy)) trees, unNextUV ss, ) <$>
    if null substs then
      pure Nothing
    else
      pure (Just substs)

data SearchNode
  = Atom C.Term C.Term
  | Fail

failSearch :: Search sig m => m a
failSearch = ask >>= \tid -> withId tid (addNode Fail) *> empty

makeTrees :: Natural -> Map.Map Natural (SearchNode, Natural) -> [Tree SearchNode]
makeTrees tid m =
  let m' = Map.filter (\(_, tid') -> tid == tid') m
  in
    fmap
      (\(tid', (tree, cs)) -> Node tree (makeTrees tid' m))
      (Map.toList m')
