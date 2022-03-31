module Unification where

import Control.Effect.Throw
import Control.Carrier.Throw.Either(runThrow)
import Control.Effect.State
import Control.Carrier.State.Strict(runState)
import Syntax.Semantic
import Syntax.Extra
import Normalization hiding(unUVEqs)
import Data.Set qualified as Set
import Data.Map(Map)
import Data.Map qualified as Map
import Control.Monad
import Data.Foldable
import GHC.Stack
import Debug.Trace

data Substitution = Subst
  { unTypeSols :: Map Global Term
  , unStageSols :: Map Global Stage
  , unUVEqs :: Map Global Global }

instance Semigroup Substitution where
  Subst ts1 ss1 eqs1 <> Subst ts2 ss2 eqs2 = Subst (ts1 <> ts2) (ss1 <> ss2) (eqs1 <> eqs2)

instance Monoid Substitution where
  mempty = Subst mempty mempty mempty

type Unify sig m =
  ( Norm sig m
  , Has (Throw ()) sig m
  , Has (State Substitution) sig m )

putStageSol :: Unify sig m => Global -> Stage -> m ()
putStageSol gl sol = do
  sols <- get
  case Map.lookup gl (unStageSols sols) of
    Nothing -> put (sols { unStageSols = Map.insert gl sol (unStageSols sols) })
    Just sol' -> pure ()-- unifyStages sol sol'

putTypeSol :: Unify sig m => Global -> Term -> m ()
putTypeSol gl sol = do
  sols <- get
  case Map.lookup gl (unTypeSols sols) of
    Nothing -> put (sols { unTypeSols = Map.insert gl sol (unTypeSols sols) })
    Just sol' -> pure ()-- unify' sol sol'

equateUVs :: Unify sig m => Global -> Global -> m ()
equateUVs gl1 gl2 = modify (\st -> st { unUVEqs = Map.fromList [(gl1, gl2), (gl2, gl1)] <> unUVEqs st })

bind2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
bind2 f act1 act2 = do
  x <- act1
  y <- act2
  f x y

unifyStages :: Unify sig m => Stage -> Stage -> m ()
unifyStages (SUniVar gl1) (SUniVar gl2) | gl1 == gl2 = pure ()
unifyStages s1@(SUniVar gl1) s2@(SUniVar gl2) = equateUVs gl1 gl2
unifyStages (SUniVar gl) s = putStageSol gl s
unifyStages s (SUniVar gl) = putStageSol gl s
unifyStages Meta Meta = pure ()
unifyStages Object Object = pure ()
unifyStages _ _ = throwError ()

unify' :: HasCallStack => Unify sig m => Term -> Term -> m ()
unify' (UniVar gl1) (UniVar gl2) | gl1 == gl2 = pure ()
unify' term1@(UniVar gl1) term2@(UniVar gl2) = equateUVs gl1 gl2
unify' (UniVar gl) term = putTypeSol gl term
unify' term (UniVar gl) = putTypeSol gl term
unify' (MetaFunType am1 inTy1 outTy1) (MetaFunType am2 inTy2 outTy2) | am1 == am2 = do
  unify' inTy1 inTy2
  bind2 unify' (evalClosure outTy1) (evalClosure outTy2)
unify' (MetaFunIntro body1) (MetaFunIntro body2) = bind2 unify' (evalClosure body1) (evalClosure body2)
unify' (ObjectFunType inTy1 outTy1) (ObjectFunType inTy2 outTy2) = do
  unify' inTy1 inTy2
  bind2 unify' (evalClosure outTy1) (evalClosure outTy2)
unify' (ObjectFunIntro body1) (ObjectFunIntro body2) = bind2 unify' (evalClosure body1) (evalClosure body2)
unify' (MetaConstantIntro did1) (MetaConstantIntro did2) | did1 == did2 = pure ()
unify' (ObjectConstantIntro did1) (ObjectConstantIntro did2) | did1 == did2 = pure ()
unify' (TypeType s1) (TypeType s2) = unifyStages s1 s2
unify' (FreeVar lvl1) (FreeVar lvl2) | lvl1 == lvl2 = pure ()
unify' term1@(MetaFunElim lam1 arg1) term2@(MetaFunElim lam2 arg2) =
  unifyFunElims term1 lam1 arg1 term2 lam2 arg2
unify' term1@(ObjectFunElim lam1 arg1) term2@(ObjectFunElim lam2 arg2) = unifyFunElims term1 lam1 arg1 term2 lam2 arg2
unify' (IOType ty1) (IOType ty2) = unify' ty1 ty2
unify' (IOIntroPure term1) (term2) = unify' term1 term2
unify' (IOIntroBind act1 k1) (IOIntroBind act2 k2) | act1 == act2 = unify' k1 k2
unify' UnitType UnitType = pure ()
unify' UnitIntro UnitIntro = pure ()
unify' (TopVar did1 _ _) (TopVar did2 _ _) | did1 == did2 = pure ()
unify' (TopVar _ env1 term1) (TopVar _ env2 term2) = bind2 unify' (evalTop env1 term1) (evalTop env2 term2)
unify' (TopVar _ env term1) term2 = bind2 unify' (evalTop env term1) (pure term2)
unify' term1 (TopVar _ env term2) = bind2 unify' (pure term1) (evalTop env term2)
unify' EElabError _ = pure ()
unify' _ EElabError = pure ()
unify' _ _ = throwError ()

unifyFunElims :: Unify sig m => Term -> Term -> Term -> Term -> Term -> Term -> m ()
unifyFunElims term1 lam1 arg1 term2 lam2 arg2 = do
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

unify :: HasCallStack => Norm sig m => Term -> Term -> m (Maybe Substitution)
unify term1 term2 = do
  r <- runThrow @() . runState mempty $ unify' term1 term2
  case r of
    Right (subst, _) -> pure (Just subst)
    Left _ -> pure Nothing
