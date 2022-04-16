module Unification where

import Control.Effect.Error
import Control.Carrier.Error.Either(runError)
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
  , Has (Error ()) sig m
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

unifyRedexes :: Unify sig m => Redex ->  Redex -> m ()
unifyRedexes (MetaFunElim lam1 arg1) (MetaFunElim lam2 arg2) = do
  unify' lam1 lam2
  unify' arg1 arg2
unifyRedexes (ObjectFunElim lam1 arg1) (ObjectFunElim lam2 arg2) = do
  unify' lam1 lam2
  unify' arg1 arg2
unifyRedexes (CodeCoreElim quote1) (CodeCoreElim quote2) = unify' quote1 quote2
unifyRedexes (CodeLowElim quote1) (CodeLowElim quote2) = unify' quote1 quote2
unifyRedexes (GlobalVar did1) (GlobalVar did2) | did1 == did2 = pure ()

unify' :: HasCallStack => Unify sig m => Term -> Term -> m ()
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
unify' (CodeCoreType ty1) (CodeCoreType ty2) = unify' ty1 ty2
unify' (CodeLowType ty1) (CodeLowType ty2) = unify' ty1 ty2
unify' (CodeCoreIntro term1) (CodeCoreIntro term2) = unify' term1 term1
unify' (CodeLowIntro term1) (CodeLowIntro term2) = unify' term1 term1
unify' (TypeType s1) (TypeType s2) = unifyStages s1 s2
unify' (LocalVar lvl1) (LocalVar lvl2) | lvl1 == lvl2 = pure ()
unify' ElabError _ = pure ()
unify' _ ElabError = pure ()
unify' (Neutral _ (UniVar gl1)) (Neutral _ (UniVar gl2)) = equateUVs gl1 gl2
unify' (Neutral _ (UniVar gl)) sol = putTypeSol gl sol
unify' sol (Neutral _ (UniVar gl)) = putTypeSol gl sol
unify' (Neutral term1 redex1) (Neutral term2 redex2) = catchError (unifyRedexes redex1 redex2) (\() -> go) where
  go :: Unify sig m => m ()
  go = case (term1, term2) of
    (Just term1, Just term2) -> unify' term1 term2
    _ -> throwError ()
unify' (Neutral (Just term1) _) term2 = unify' term1 term2
unify' term1 (Neutral (Just term2) _) = unify' term1 term2
unify' _ _ = throwError ()

unify :: HasCallStack => Norm sig m => Term -> Term -> m (Maybe Substitution)
unify term1 term2 = do
  r <- runError @() . runState mempty $ unify' term1 term2
  case r of
    Right (subst, _) -> pure (Just subst)
    Left _ -> pure Nothing
