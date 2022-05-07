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

data SearchState = SearchState
  { unNextUV :: Natural }

type Search sig m =
  ( Alternative m
  , Has NonDet sig m
  , Norm sig m
  , Has (State SearchState) sig m )

prove :: forall sig m. Search sig m => Seq Term -> Term -> m (Map.Map Global Term)
prove ctx (Neutral (Just p) _) =
  prove ctx p
prove ctx (Rigid (ConjType p q)) =
  (<>) <$> prove ctx p <*> prove ctx q
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
prove ctx goal = do
  substs <- filterTraverse go ctx
  oneOf substs
  where
    go :: Search sig m => Term -> m (Maybe (Map.Map Global Term))
    go (Neutral (Just p) _) = go p
    go (Rigid (ImplType p q)) = do
      subst <- go q
      traverse (\s -> (<>) <$> prove ctx p <*> pure s) subst
    go p = fmap (fmap \(Subst ts _ _) -> ts) (unify goal p)

freshUV :: Search sig m => m Term
freshUV = do
  state <- get
  put (state { unNextUV = unNextUV state + 1 })
  pure (Neutral Nothing . UniVar . Global $ unNextUV state)

isAtomic :: Term -> Bool
isAtomic (MetaFunElims (Rigid (PropConstIntro _)) _) = True
isAtomic _ = False

prove' :: Seq Term -> Term -> Natural -> Seq (Map.Map Global Term)
prove' ctx goal nuv =
  run .
  runNonDetA .
  evaSltate (SearchState nuv) .
  runReader (NormContext (Env mempty mempty) mempty mempty mempty) $
  prove ctx goal
