module Search where

import Syntax.Semantic
import Control.Effect.NonDet(NonDet, Alternative, empty, (<|>), oneOf)
import Control.Effect.State(State, get, put, modify)
import Control.Algebra(Has)
import Normalization
import Unification
import Data.Map qualified as Map
import Syntax.Common(Global(..))
import Numeric.Natural
import Data.Sequence hiding(empty)
import Extra

data SearchState = SearchState
  { unSols :: Map.Map Global Term
  , unNextUV :: Natural }

type Search sig m =
  ( Alternative m
  , Has NonDet sig m
  , Norm sig m
  , Has (State SearchState) sig m )

prove :: forall sig m. Search sig m => Seq Term -> Term -> m ()
prove ctx (Neutral (Just p) _) =
  prove ctx p
prove ctx (Rigid (ConjType p q)) = do
  prove ctx p
  prove ctx q
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
  Subst sols _ _ <- oneOf substs
  modify (\st -> st { unSols = sols <> unSols st })
  where
    go :: Search sig m => Term -> m (Maybe Substitution)
    go (Neutral (Just p) _) = go p
    go (Rigid (ImplType p q)) = do
      prove ctx p
      go q
    go p = unify goal p 

freshUV :: Search sig m => m Term
freshUV = do
  state <- get
  put (state { unNextUV = unNextUV state + 1 })
  pure (Neutral Nothing . UniVar . Global $ unNextUV state)

isAtomic :: Term -> Bool
isAtomic (MetaFunElims (Rigid (PropConstIntro _)) _) = True
isAtomic _ = False
