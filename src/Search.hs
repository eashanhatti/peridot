module Search where

import Syntax.Semantic
import Control.Effect.NonDet(NonDet, Alternative, empty, (<|>), oneOf)
import Control.Effect.State(State, get, put, modify)
import Control.Carrier.NonDet.Church
import Control.Carrier.State.Strict
import Control.Carrier.Reader
import Control.Algebra(Has, run)
import Normalization
import Unification
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

prove :: forall sig m. Search sig m => Seq Term -> Term -> m (Map.Map Global Term)
prove ctx (Neutral p _) = do
  p <- force p
  case p of
    Just p -> prove ctx p
    Nothing -> empty
prove ctx (Rigid (ConjType p q)) =
  (<>) <$> prove ctx p <*> prove ctx q
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
prove ctx goal | isAtomic (traceWith shower goal) = do
  substs <- filterTraverse (\ty -> go ctx goal (traceWith shower ty)) ctx
  oneOf substs
prove _ goal = empty

go :: Search sig m => Seq Term -> Term -> Term -> m (Maybe (Map.Map Global Term))
go ctx goal (Neutral p _) = do
  p <- force p
  case p of
    Just p -> go ctx goal p
    Nothing -> empty
go ctx goal (Rigid (AllType (MetaFunIntro p))) = do
  uv <- freshUV
  vP <- appClosure p uv
  go ctx goal vP
go ctx goal (Rigid (ImplType p q)) = do
  subst <- go ctx goal q
  traverse (\s -> (<>) <$> prove ctx p <*> pure s) subst
go ctx (MetaFunElims gHead gArgs) (MetaFunElims dHead dArgs)
  | length dArgs == length gArgs
  = do
    substs <- traverse (\(dArg, gArg) -> unify gArg dArg) (zip dArgs gArgs)
    -- let !() = trace (shower (zip dArgs gArgs)) ()
    -- let !() = trace (shower substs) ()
    pure
      (fmap concat .
      fmap (fmap \(Subst ts _ _) -> ts) .
      allJustOrNothing $
      substs)
go _ g d = empty

freshUV :: Search sig m => m Term
freshUV = do
  state <- get
  put (state { unNextUV = unNextUV state + 1 })
  pure (Neutral (pure Nothing) . UniVar . Global $ unNextUV state)

isAtomic :: Term -> Bool
isAtomic (MetaFunElims _ _) = True
isAtomic _ = False

proveDet :: Norm sig m => Seq Term -> Term -> m (Seq (Map.Map Global Term))
proveDet ctx goal =
  runNonDetA .
  evalState (SearchState 2000) $
  prove ctx goal
