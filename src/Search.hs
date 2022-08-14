module Search where

import Data.Maybe
import Syntax.Semantic
import Control.Effect.Lift
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
import Data.Text(pack)

data SearchState = SearchState
  { unNextUV :: Natural
  , unNextId :: Natural
  , unTree :: Map.Map Natural (SearchNode, Natural)}

type Search sig m =
  ( Alternative m
  , Has NonDet sig m
  , Norm sig m
  , Has (Lift IO) sig m
  , Has (Reader Natural) sig m
  , Has (State SearchState) sig m )

type Substitution = (Map.Map Global UVSolution, Map.Map Global (Set.Set Global))

eToM (Right x) = Just x
eToM (Left _) = Nothing

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
        Just (unTerm -> sol') -> isNothing . eToM <$> unifyRS sol sol'
        Nothing -> pure False
  if fmap fst overlap /= mempty then
    throwError ()
  else
    pure (ts <> ts', Map.unionWith (<>) eqs eqs')

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
    cGoal <- readback goal
    let !_ = tracePretty cGoal
    def <- oneOf ctx
    ls <- Syntax.Semantic.unLocals . unEnv <$> ask
    snd <$> local
      (\ctx -> ctx
        { unEnv = Env mempty (Syntax.Semantic.unGlobals . unEnv $ ctx) })
      (search ctx ls cGoal def)) <|>
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
  n <- freshId
  let c = Rigid . MetaConstIntro . Id $ n
  vP <- appClosure p c
  define c (prove ctx vP)
prove ctx (Rigid (PropIdType x y)) = do
  r <- eToM <$> unifyRS x y
  case r of
    Just (Subst ts eqs) -> pure (ts, eqs)
    Nothing -> empty
prove ctx (Rigid (Iterate p e (MetaFunIntro q))) = do
  substs <-
    runNonDetA @Seq $
    prove ctx p
  subst <- oneOf substs
  e' <-
    local
      (\ctx -> ctx
        { unTypeUVs = fst subst <> unTypeUVs ctx
        , unUVEqs = snd subst <> unUVEqs ctx })
      (zonk e >>= eval)
  subst' <- oneOf substs
  q' <- appClosure q e'
  subst'' <- withSubst subst' (prove ctx q')
  unionSubsts subst'' subst'

prove _ MetaTypeType = pure mempty
prove _ goal = empty

search :: Search sig m => Seq Term -> Seq Term -> C.Term -> Term -> m (Natural, Substitution)
search ctx gEnv g@(C.MetaFunElims gHead gArgs) d@(MetaFunElims dHead dArgs)
  | length dArgs == length gArgs
  = do
    normCtx <- ask
    let tuvs = unTypeUVs normCtx
    let eqs = unUVEqs normCtx
    vGHead <-
      local
        (\ctx -> ctx { unEnv = Env gEnv (unGlobals . unEnv $ ctx) })
        (eval gHead)
    vGArgs <-
      traverse
        (\arg -> local
          (\ctx -> ctx { unEnv = Env gEnv (unGlobals . unEnv $ ctx) })
          (eval arg))
        gArgs
    -- substs <-
    --   traverse
    --     (\(dArg, gArg) -> eToM <$> unifyRS gArg dArg)
    --     (zip dArgs vGArgs)
    substs <-
      traverse
        (\(dArg, gArg) -> do
          r <- unifyRS gArg dArg
          pure case r of
            Right x -> Just x
            Left e -> {-trace (shower (e, gArg, dArg)) -}Nothing)
        (zip dArgs vGArgs)
    -- let !_ = tracePrettyS "DEF" d
    -- let !_ = tracePrettyS "GOAL" g
    substs <- ((<| substs) <$> (eToM <$> unifyRS vGHead dHead))
    tid <- case head substs of
      Just _ -> do
        -- let !_ = tracePrettyS "CTX" gEnv
        -- vG <- eval g
        -- let !_ = tracePrettyS "GOALS" (g, (vGHead, vGArgs))
        -- let def = Map.lookup (LVGlobal 2092) (unTypeUVs normCtx)
        -- !_ <- tracePrettyS "CTX" <$> (traverse (normalize >=> eval) (fmap unTerm def))
        -- let !_ = tracePrettyS "DARGS" (dHead <| dArgs)
        -- let !_ = tracePrettyS "GARGS" (vGHead <| vGArgs)
        -- let !_ = tracePrettyS "SUBSTS" substs
        cD <- zonk d
        g' <- eval g >>= zonk
        tid <- addNode (Atom cD g')
        case allJustOrNothing (tail substs) of
          Just _ -> pure tid
          Nothing -> withId tid (addNode Fail) *> pure 0
      Nothing -> pure 0
    case allJustOrNothing substs of
      Just substs ->
        (tid ,) <$>
          (concatSubsts'' (fmap (\(Subst ts eqs) -> (ts, eqs)) substs) >>= \case
            Just r -> do
              pure r
            Nothing -> withId tid (addNode Fail) *> empty)
      Nothing -> empty
search ctx gEnv goal (MetaFunType _ _ p) = do
  uv <- freshUV
  -- case uv of
  --   Neutral _ (UniVar (LVGlobal 2185) _) -> do
  --     let !_ = tracePretty p
  --     pure ()
  --   _ -> pure ()
  n <- unNextUV <$> get
  vP <- appClosure p uv
  define uv (search ctx (gEnv |> Rigid (Dummy (pack . show $ n))) goal vP)
search ctx gEnv goal (Rigid (ImplType p q)) = do
  (tid, qSubst) <- search ctx gEnv goal q
  pSubst <- withId tid . withSubst qSubst $ prove ctx p
  (tid ,) <$> qSubst `unionSubsts` pSubst
search ctx gEnv goal (Neutral p _) = do
  p <- force p
  case p of
    Just p -> search ctx gEnv goal p
    Nothing -> empty
search _ _ C.MetaTypeType _ = pure (0, mempty)
search _ _ _ _ = empty

freshUV :: Search sig m => m Term
freshUV = do
  state <- get
  put (state { unNextUV = unNextUV state + 1 })
  pure
    (Neutral (uvRedex . LVGlobal $ unNextUV state) .
    flip UniVar (Just (Rigid (Dummy "uvtype"))) .
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
  (Has (Lift IO) sig m, Norm sig m) =>
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
  (Node (Atom (C.Rigid (C.Dummy "def")) cGoal) trees, unNextUV ss, ) <$>
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
