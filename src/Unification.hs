module Unification where

import Control.Effect.Throw
import Control.Carrier.Throw.Either(runThrow)
import Control.Effect.State
import Control.Carrier.State.Strict(runState)
import Syntax.Semantic
import Syntax.Extra
import Normalization
import Data.Map(Map)
import Data.Map qualified as Map
import Control.Monad
import Data.Foldable

data Substitution = Subst
  { unTypeSols :: Map Global Term
  , unStageSols :: Map Global Stage
  , unRepSols :: Map Global RuntimeRep }

instance Semigroup Substitution where
  Subst ts1 ss1 rs1 <> Subst ts2 ss2 rs2 = Subst (ts1 <> ts2) (ss1 <> ss2) (rs1 <> rs2)

instance Monoid Substitution where
  mempty = Subst mempty mempty mempty

type Unify sig m =
  ( Norm sig m
  , Has (Throw ()) sig m
  , Has (State Substitution) sig m )

putRepSol :: Unify sig m => Global -> RuntimeRep -> m ()
putRepSol gl sol = do
  sols <- get
  put (sols { unRepSols = Map.insert gl sol (unRepSols sols) })

putStageSol :: Unify sig m => Global -> Stage -> m ()
putStageSol gl sol = do
  sols <- get
  put (sols { unStageSols = Map.insert gl sol (unStageSols sols) })

putTypeSol :: Unify sig m => Global -> Term -> m ()
putTypeSol gl sol = do
  sols <- get
  put (sols { unTypeSols = Map.insert gl sol (unTypeSols sols) })

bind2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
bind2 f act1 act2 = do
  x <- act1
  y <- act2
  f x y

unifyReps :: Unify sig m => RuntimeRep -> RuntimeRep -> m ()
unifyReps (RUniVar gl1) (RUniVar gl2) | gl1 == gl2 = pure ()
unifyReps rep1@(RUniVar gl1) rep2@(RUniVar gl2) = do
  putRepSol gl1 rep2
  putRepSol gl2 rep1
unifyReps (RUniVar gl) rep = putRepSol gl rep
unifyReps rep (RUniVar gl) = putRepSol gl rep
unifyReps Ptr Ptr = pure ()
unifyReps Lazy Lazy = pure ()
unifyReps Word Word = pure ()
unifyReps Erased Erased = pure ()
unifyReps (Prod reps1) (Prod reps2) | length reps1 == length reps2 = traverse_ (uncurry unifyReps) (zip reps1 reps2)
unifyReps (Sum reps1) (Sum reps2) | length reps1 == length reps2 = traverse_ (uncurry unifyReps) (zip reps1 reps2)
unifyReps _ _ = throwError ()

unifyStages :: Unify sig m => Stage -> Stage -> m ()
unifyStages (SUniVar gl1) (SUniVar gl2) | gl1 == gl2 = pure ()
unifyStages s1@(SUniVar gl1) s2@(SUniVar gl2) = do
  putStageSol gl1 s2
  putStageSol gl2 s1
unifyStages (SUniVar gl) s = putStageSol gl s
unifyStages s (SUniVar gl) = putStageSol gl s
unifyStages Meta Meta = pure ()
unifyStages (Object rep1) (Object rep2) = unifyReps rep1 rep2
unifyStages _ _ = throwError ()

unify' :: Unify sig m => Term -> Term -> m ()
unify' (UniVar gl1) (UniVar gl2) | gl1 == gl2 = pure ()
unify' term1@(UniVar gl1) term2@(UniVar gl2) = do
  putTypeSol gl1 term2
  putTypeSol gl2 term1
unify' (UniVar gl) term = putTypeSol gl term
unify' term (UniVar gl) = putTypeSol gl term
unify' (FunType am1 inTy1 outTy1) (FunType am2 inTy2 outTy2) | am1 == am2 = do
  unify' inTy1 inTy2
  bind2 unify' (evalClosure outTy1) (evalClosure outTy2)
unify' (FunIntro _ body1) (FunIntro _ body2) = bind2 unify' (evalClosure body1) (evalClosure body2)
unify' (MetaConstantIntro did1) (MetaConstantIntro did2) | did1 == did2 = pure ()
unify' (ObjectConstantIntro did1) (ObjectConstantIntro did2) | did1 == did2 = pure ()
unify' (TypeType s1) (TypeType s2) = unifyStages s1 s2
unify' (FreeVar lvl1) (FreeVar lvl2) | lvl1 == lvl2 = pure ()
unify' term1@(FunElim lam1 arg1) term2@(FunElim lam2 arg2) = do
  r1 <- unify lam1 lam2
  case r1 of
    Just subst -> do
      modify (subst <>)
      unify' arg1 arg2
    Nothing -> do
      term1 <- normalize term1
      term2 <- normalize term2
      r2 <- unify term1 term2
      case r2 of
        Just subst -> modify (subst <>)
        Nothing -> throwError ()
unify' (IOType ty1) (IOType ty2) = unify' ty1 ty2
unify' (IOIntro1 term1) (term2) = unify' term1 term2
unify' (IOIntro2 act1 k1) (IOIntro2 act2 k2) | act1 == act2 = unify' k1 k2
unify' UnitType UnitType = pure ()
unify' UnitIntro UnitIntro = pure ()
unify' (TopVar did1 _ _) (TopVar did2 _ _) | did1 == did2 = pure ()
unify' (TopVar _ env1 term1) (TopVar _ env2 term2) = bind2 unify' (evalTop env1 term1) (evalTop env2 term2)
unify' (TopVar _ env term1) term2 = bind2 unify' (evalTop env term1) (pure term2)
unify' term1 (TopVar _ env term2) = bind2 unify' (pure term1) (evalTop env term2)
unify' EElabError _ = pure ()
unify' _ EElabError = pure ()
unify' _ _ = throwError ()

unify :: Norm sig m => Term -> Term -> m (Maybe Substitution)
unify term1 term2 = do
  r <- runThrow @() . runState mempty $ unify' term1 term2
  case r of
    Right (subst, _) -> pure (Just subst)
    Left _ -> pure Nothing
