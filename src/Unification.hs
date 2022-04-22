module Unification where

import Control.Effect.Error
import Control.Carrier.Error.Either(runError)
import Control.Effect.State
import Control.Carrier.State.Strict(runState)
import Syntax.Semantic
import Syntax.Common
import Normalization hiding(unUVEqs)
import Data.Set qualified as Set
import Data.Map(Map)
import Data.Map qualified as Map
import Control.Monad
import Data.Foldable
import GHC.Stack
import Debug.Trace
import Data.Sequence
import Prelude hiding(zip)

data Substitution = Subst
  { unTypeSols :: Map Global Term
  , unStageSols :: Map Global Stage
  , unVCSols :: Map Global ValueCategory
  , unUVEqs :: Map Global Global }

instance Semigroup Substitution where
  Subst ts1 ss1 vcs1 eqs1 <> Subst ts2 ss2 vcs2 eqs2 = Subst (ts1 <> ts2) (ss1 <> ss2) (vcs1 <> vcs2) (eqs1 <> eqs2)

instance Monoid Substitution where
  mempty = Subst mempty mempty mempty mempty

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

putVCSol :: Unify sig m => Global -> ValueCategory -> m ()
putVCSol gl sol = do
  sols <- get
  case Map.lookup gl (unVCSols sols) of
    Nothing -> put (sols { unVCSols = Map.insert gl sol (unVCSols sols) })
    Just sol' -> pure ()

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
unifyStages Obj Obj = pure ()
unifyStages (Low l1) (Low l2) | l1 == l2 = pure ()
unifyStages _ _ = throwError ()

unifyRedexes :: Unify sig m => Redex ->  Redex -> m ()
unifyRedexes (MetaFunElim lam1 arg1) (MetaFunElim lam2 arg2) = do
  unify' lam1 lam2
  unify' arg1 arg2
unifyRedexes (ObjFunElim lam1 arg1) (ObjFunElim lam2 arg2) = do
  unify' lam1 lam2
  unify' arg1 arg2
unifyRedexes (CodeCoreElim quote1) (CodeCoreElim quote2) = unify' quote1 quote2
unifyRedexes (CodeLowCTmElim quote1) (CodeLowCTmElim quote2) = unify' quote1 quote2
unifyRedexes (GlobalVar did1) (GlobalVar did2) | did1 == did2 = pure ()

unifyStmts :: Unify sig m => CStatement Term -> CStatement Term -> m ()
unifyStmts (VarDecl ty1) (VarDecl ty2) = unify' ty1 ty2
unifyStmts (Assign var1 val1) (Assign var2 val2) = do
  unify' var1 var2
  unify' val1 val2
unifyStmts (If cond1 trueBody1 falseBody1) (If cond2 trueBody2 falseBody2) = do
  unify' cond1 cond2
  unifyStmts trueBody1 trueBody2
  unifyStmts falseBody1 falseBody2
unifyStmts (Block lstmt1 rstmt1) (Block lstmt2 rstmt2) = do
  unifyStmts lstmt1 lstmt2
  unifyStmts rstmt1 rstmt2
unifyStmts (Return (Just val1)) (Return (Just val2)) = unify' val1 val2
unifyStmts (Return Nothing) (Return Nothing) = pure ()
unifyStmts (CodeLowCStmtElim quote1) (CodeLowCStmtElim quote2) = unify' quote1 quote2

unifyVCs :: Unify sig m => ValueCategory -> ValueCategory -> m ()
unifyVCs (VCUniVar gl1) (VCUniVar gl2) = equateUVs gl1 gl2
unifyVCs (VCUniVar gl) vc = putVCSol gl vc
unifyVCs vc (VCUniVar gl) = putVCSol gl vc
unifyVCs RVal RVal = pure ()
unifyVCs LVal LVal = pure ()
unifyVCs _ _ = throwError ()

unifyOps :: Unify sig m => COp Term -> COp Term -> m ()
unifyOps (Ref term1) (Ref term2) = unify' term1 term2
unifyOps (Deref term1) (Deref term2) = unify' term1 term2
unifyOps (Add x1 y1) (Add x2 y2) = do
  unify' x1 x2
  unify' y1 y2
unifyOps (Sub x1 y1) (Sub x2 y2) = do
  unify' x1 x2
  unify' y1 y2
unifyOps (Less x1 y1) (Less x2 y2) = do
  unify' x1 x2
  unify' y1 y2
unifyOps (Grtr x1 y1) (Grtr x2 y2) = do
  unify' x1 x2
  unify' y1 y2
unifyOps (Eql x1 y1) (Eql x2 y2) = do
  unify' x1 x2
  unify' y1 y2

unify' :: HasCallStack => Unify sig m => Term -> Term -> m ()
unify' (MetaFunType am1 inTy1 outTy1) (MetaFunType am2 inTy2 outTy2) | am1 == am2 = do
  unify' inTy1 inTy2
  bind2 unify' (evalClosure outTy1) (evalClosure outTy2)
unify' (MetaFunIntro body1) (MetaFunIntro body2) = bind2 unify' (evalClosure body1) (evalClosure body2)
unify' (ObjFunType inTy1 outTy1) (ObjFunType inTy2 outTy2) = do
  unify' inTy1 inTy2
  bind2 unify' (evalClosure outTy1) (evalClosure outTy2)
unify' (ObjFunIntro body1) (ObjFunIntro body2) = bind2 unify' (evalClosure body1) (evalClosure body2)
unify' (MetaConstIntro did1) (MetaConstIntro did2) | did1 == did2 = pure ()
unify' (ObjConstIntro did1) (ObjConstIntro did2) | did1 == did2 = pure ()
unify' (CodeCoreType ty1) (CodeCoreType ty2) = unify' ty1 ty2
unify' (CodeLowCTmType ty1) (CodeLowCTmType ty2) = unify' ty1 ty2
unify' (CodeCoreIntro term1) (CodeCoreIntro term2) = unify' term1 term1
unify' (CodeLowCTmIntro term1) (CodeLowCTmIntro term2) = unify' term1 term1
unify' (CodeLowCStmtType ty1) (CodeLowCStmtType ty2) = unify' ty1 ty2
unify' (CodeLowCStmtIntro stmt1) (CodeLowCStmtIntro stmt2) = unifyStmts stmt1 stmt2
unify' (CPtrType ty1) (CPtrType ty2) = unify' ty1 ty2
unify' CIntType CIntType = pure ()
unify' CVoidType CVoidType = pure ()
unify' (CValType vc1 ty1) (CValType vc2 ty2) = do
  unifyVCs vc1 vc2
  unify' ty1 ty2
unify' (CFunType inTys1 outTy1) (CFunType inTys2 outTy2) = do
  traverse (uncurry unify') (zip inTys1 inTys2)
  unify' outTy1 outTy2
unify' (CIntIntro x1) (CIntIntro x2) | x1 == x2 = pure ()
unify' (COp op1) (COp op2) = unifyOps op1 op2
unify' (CFunCall fn1 args1) (CFunCall fn2 args2) = do
  unify' fn1 fn2
  traverse_ (uncurry unify') (zip args1 args2)
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
