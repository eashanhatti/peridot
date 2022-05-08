module Search where

import Syntax.Semantic
import Control.Effect.NonDet(NonDet, Alternative, empty, (<|>), oneOf)
import Control.Effect.State(State, get, put, modify)
import Control.Carrier.NonDet.Church
import Control.Carrier.State.Strict
import Control.Carrier.Reader
import Control.Algebra(Has, run)
import Normalization
import Unification hiding(Substitution)
import Data.Map qualified as Map
import Syntax.Common(Global(..))
import Numeric.Natural
import Data.Sequence hiding(empty)
import Extra
import Debug.Trace
import Shower
import Prelude hiding(length, zip, concatMap, concat)

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
        substs <- filterTraverse (search ctx goal{- . (traceWith (("DEF"++) . shower))-}) ctx
        oneOf substs
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
prove _ goal = empty

search :: Search sig m => Seq Term -> Term -> Term -> m (Maybe Substitution)
search ctx (MetaFunElims gHead gArgs) (MetaFunElims dHead dArgs)
  | length dArgs == length gArgs
  = do
    {-normCtx <- ask-}
    {-let !() = trace (shower (unTypeUVs normCtx)) ()-}
    substs <-
      traverse
        (\(dArg, gArg) -> unify gArg dArg)
        ({-traceWith (("ARGS"++) . shower) $ -}zip dArgs gArgs)
    substs <- (<| substs) <$> unify gHead dHead
    pure
      (fmap concat .
      fmap (fmap \(Subst ts _ _) -> ts) .
      allJustOrNothing $
      {-traceWith (("SUBSTS"++) . shower) -}substs)
search ctx goal (Rigid (AllType (MetaFunIntro p))) = do
  uv <- freshUV
  vP <- appClosure p uv
  search ctx goal vP
search ctx goal (Rigid (ImplType p q)) = do
  qSubst <- search ctx goal q
  case qSubst of
    Just qSubst -> do
      pSubst <- withSubst qSubst (prove ctx p)
      pure (Just (qSubst `Map.union` pSubst))
    Nothing -> pure Nothing
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
  pure (Neutral (uvRedex . Global $ unNextUV state) . UniVar . Global $ unNextUV state)

isAtomic :: Term -> Bool
isAtomic (MetaFunElims _ _) = True
isAtomic _ = False

proveDet :: Norm sig m => Seq Term -> Term -> m (Seq Substitution)
proveDet ctx goal =
  runNonDetA .
  evalState (SearchState 2000) $
  prove ctx goal
