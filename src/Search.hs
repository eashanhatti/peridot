module Search where

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
import Syntax.Common(Global(..))
import Numeric.Natural
import Data.Sequence hiding(empty)
import Extra
import Debug.Trace
import Control.Applicative
import Shower
import Prelude hiding(length, zip, concatMap, concat, filter, null)
import Data.Bifunctor
import Data.Foldable(foldl')
import PrettyPrint

data SearchState = SearchState
  { unNextUV :: Natural }

type Search sig m =
  ( Alternative m
  , Has NonDet sig m
  , Norm sig m
  , Has (State SearchState) sig m )

type Substitution = (Map.Map Global Term, Map.Map Global Global)

withSubst :: Search sig m => Substitution -> m Substitution -> m Substitution
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
prove ctx goal@(Neutral p _) = do
  def <- oneOf ctx
  search ctx goal def <|> do
    p <- force p
    case p of
      Just p -> prove ctx p
      Nothing -> empty
prove ctx (Rigid (ConjType p q)) = do
  subst <- prove ctx p
  withSubst subst (prove ctx q)
prove ctx (Rigid (DisjType p q)) =
  prove ctx p <|> prove ctx q
prove ctx (Rigid (SomeType (MetaFunIntro p))) = do
  uv <- freshUV
  vP <- appClosure p uv
  prove ctx vP
prove ctx (Rigid (ImplType p q)) =
  prove (p <| ctx) q
prove ctx (Rigid (AllType (MetaFunIntro p))) = do
  vP <- evalClosure p
  prove ctx vP
prove ctx (Rigid (PropIdType x y)) = do
  r <- unifyR x y
  case r of
    Just (Subst ts eqs) -> pure (ts, eqs)
    Nothing -> empty
prove _ goal = empty

search :: Search sig m => Seq Term -> Term -> Term -> m Substitution
search ctx g@(MetaFunElims gHead gArgs) d@(MetaFunElims dHead dArgs)
  | length dArgs == length gArgs
  = do
    -- normCtx <- ask
    -- let !_ = tracePrettyS "CTX" (unTypeUVs normCtx)
    -- let !_ = tracePrettyS "DARGS" (dHead <| dArgs)
    -- let !_ = tracePrettyS "GARGS" (dHead <| gArgs)
    substs <-
      traverse
        (\(dArg, gArg) -> unifyR gArg dArg)
        (zip dArgs gArgs)
    -- let !_ = tracePrettyS "DEF" d
    -- let !_ = tracePrettyS "GOAL" g
    substs <- ((<| substs) <$> unifyR gHead dHead)
    -- let !_ = tracePrettyS "SUBSTS" substs
    case allJustOrNothing substs of
      Just substs ->
        pure (concatSubsts (fmap (\(Subst ts eqs) -> (ts, eqs)) substs))
      Nothing -> empty
search ctx goal (Rigid (AllType (MetaFunIntro p))) = do
  uv <- freshUV
  vP <- appClosure p uv
  search ctx goal vP
search ctx goal (Rigid (ImplType p q)) = do
  qSubst <- search ctx goal q
  pSubst <- withSubst qSubst (prove ctx p)
  pure (qSubst `unionSubsts` pSubst)
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
    UniVar .
    LVGlobal $
    unNextUV state)

isAtomic :: Term -> Bool
isAtomic (MetaFunElims _ _) = True
isAtomic _ = False

proveDet :: Norm sig m => Seq Term -> Term -> m (Maybe (Seq Substitution))
proveDet ctx goal = do
  substs <-
    runNonDetA .
    evalState (SearchState 2000) $
    prove ctx goal
  if null substs then
    pure Nothing
  else
    pure (Just substs)
