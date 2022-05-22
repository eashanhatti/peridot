module Search where

import Syntax.Semantic
import Control.Effect.NonDet(NonDet, Alternative, empty, (<|>), oneOf)
import Control.Effect.State(State, get, put, modify)
import Control.Carrier.NonDet.Church
import Control.Carrier.State.Strict
import Control.Carrier.Reader
import Control.Effect.Throw
import Control.Algebra(Has, run)
import Normalization
import Unification hiding(Substitution)
import Data.Map qualified as Map
import Syntax.Common(Global(..))
import Numeric.Natural
import Data.Sequence hiding(empty)
import Extra
import Debug.Trace
import Control.Applicative
import Shower
import Prelude hiding(length, zip, concatMap, concat, filter, null)

data SearchState = SearchState
  { unNextUV :: Natural }

type Search sig m =
  ( Alternative m
  , Has NonDet sig m
  , Norm sig m
  , Has (State SearchState) sig m )

type Substitution = Map.Map Global Term

withSubst :: Search sig m => Substitution -> m Substitution -> m Substitution
withSubst subst = local (\ctx -> ctx { unTypeUVs = subst `Map.union` (unTypeUVs ctx) })

prove :: forall sig m. Search sig m => Seq Term -> Term -> m Substitution
prove ctx goal@(Neutral p _) = do
  p <- force p
  case p of
    Just p -> prove ctx p
    Nothing ->
      if isAtomic goal then do
        def <- oneOf ctx
        search ctx goal def
      else
        empty
prove ctx (Rigid (ConjType p q)) = do
  subst <- prove ctx p
  withSubst subst (prove ctx q)
prove ctx (Rigid (DisjType p q)) =
  prove ctx p <|> prove ctx q
prove ctx (Rigid (SomeType (MetaFunIntro p))) = do
  -- uv <- freshUV
  vP <- evalClosure p {-uv-}
  prove ctx vP
prove ctx (Rigid (ImplType p q)) =
  prove (p <| ctx) q
prove ctx (Rigid (AllType (MetaFunIntro p))) = do
  uv <- freshUV
  vP <- appClosure p uv
  prove ctx vP
prove ctx (Rigid (PropIdType x y)) = do
  r <- unify x y
  case r of
    Just (Subst ts _ _) -> pure ts
    Nothing -> empty
prove _ goal = empty

search :: Search sig m => Seq Term -> Term -> Term -> m Substitution
search ctx (MetaFunElims gHead gArgs) (MetaFunElims dHead dArgs)
  | length dArgs == length gArgs
  = do
    normCtx <- ask
    let !_ = tracePrettyS "CTX" (unTypeUVs normCtx)
    substs <-
      traverse
        (\(dArg, gArg) -> unify gArg dArg)
        (zip dArgs gArgs)
    let !_ = tracePrettyS "DARGS" (dHead <| dArgs)
    let !_ = tracePrettyS "GARGS" (dHead <| gArgs)
    substs <- ((<| substs) <$> unify gHead dHead)
    let !_ = tracePrettyS "SUBSTS" substs
    case allJustOrNothing substs of
      Just substs -> pure (concat (fmap (\(Subst ts _ _) -> ts) substs))
      Nothing -> empty
search ctx goal (Rigid (AllType (MetaFunIntro p))) = do
  uv <- freshUV
  vP <- appClosure p uv
  search ctx goal vP
search ctx goal (Rigid (ImplType p q)) = do
  qSubst <- search ctx goal q
  pSubst <- withSubst qSubst (prove ctx p)
  pure (qSubst `Map.union` pSubst)
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
