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

type Substitution = Map Global Term

type Unify sig m =
  ( Norm sig m
  , Has (Throw ()) sig m
  , Has (State Substitution) sig m )

putSol :: Unify sig m => Global -> Term -> m ()
putSol gl sol = do
  sols <- get
  put (Map.insert gl sol sols)

bind2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
bind2 f act1 act2 = do
  x <- act1
  y <- act2
  f x y

unify' :: Unify sig m => Term -> Term -> m ()
unify' term1@(UniVar gl1) term2@(UniVar gl2) = do
  putSol gl1 term2
  putSol gl2 term1
unify' (UniVar gl) term = putSol gl term
unify' term (UniVar gl) = putSol gl term
unify' (FunType am1 inTy1 outTy1) (FunType am2 inTy2 outTy2) | am1 == am2 = do
  unify' inTy1 inTy2
  bind2 unify' (evalClosure outTy1) (evalClosure outTy2)
unify' (FunIntro body1) (FunIntro body2) = bind2 unify' (evalClosure body1) (evalClosure body2)
unify' (MetaConstantIntro did1) (MetaConstantIntro did2) | did1 == did2 = pure ()
unify' (ObjectConstantIntro did1) (ObjectConstantIntro did2) | did1 == did2 = pure ()
unify' (TypeType s1) (TypeType s2) | s1 == s2 = pure ()
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
unify' (IOIntro2 act1 k1) (IOIntro2 act2 k2) = do
  unify' act1 act2
  unify' k1 k2
unify' (IOIntro3 op1) (IOIntro3 op2) | op1 == op2 = pure ()
unify' UnitType UnitType = pure ()
unify' UnitIntro UnitIntro = pure ()
unify' (TopVar did1 _ _) (TopVar did2 _ _) | did1 == did2 = pure ()
unify' (TopVar _ env1 term1) (TopVar _ env2 term2) = bind2 unify' (evalTop env1 term1) (evalTop env2 term2)
unify' (TopVar _ env term1) term2 = bind2 unify' (evalTop env term1) (pure term2)
unify' term1 (TopVar _ env term2) = bind2 unify' (pure term1) (evalTop env term2)
unify' _ _ = throwError ()

unify :: Norm sig m => Term -> Term -> m (Maybe Substitution)
unify term1 term2 = do
  r <- runThrow @() . runState mempty $ unify' term1 term2
  case r of
    Right (subst, _) -> pure (Just subst)
    Left _ -> pure Nothing