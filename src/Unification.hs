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
import Control.Applicative
import Prelude hiding(zip)

data Substitution = Subst
  { unTypeSols :: Map Global Term
  , unUnivSols :: Map Global Universe
  -- , unVCSols :: Map Global ValueCategory
  , unUVEqs :: Map Global Global }
  deriving (Show)

instance Semigroup Substitution where
  Subst ts1 ss1 {-vcs1-} eqs1 <> Subst ts2 ss2 {-vcs2-} eqs2 = Subst (ts1 <> ts2) (ss1 <> ss2) {-(vcs1 <> vcs2)-} (eqs1 <> eqs2)

instance Monoid Substitution where
  mempty = Subst mempty mempty {-mempty-} mempty

type Unify sig m =
  ( Norm sig m
  , Has (Error ()) sig m
  , Has (State Substitution) sig m )

putUniverseSol :: Unify sig m => Global -> Universe -> m ()
putUniverseSol gl sol = do
  sols <- get
  case Map.lookup gl (unUnivSols sols) of
    Nothing -> put (sols { unUnivSols = Map.insert gl sol (unUnivSols sols) })
    Just sol' -> pure ()-- unifyUnivs sol sol'

putTypeSol :: Unify sig m => Global -> Term -> m ()
putTypeSol gl sol = do
  sols <- get
  case Map.lookup gl (unTypeSols sols) of
    Nothing -> put (sols { unTypeSols = Map.insert gl sol (unTypeSols sols) })
    Just sol' -> unify' sol sol'

-- putVCSol :: Unify sig m => Global -> ValueCategory -> m ()
-- putVCSol gl sol = do
--   sols <- get
--   case Map.lookup gl (unVCSols sols) of
--     Nothing -> put (sols { unVCSols = Map.insert gl sol (unVCSols sols) })
--     Just sol' -> pure ()

equateUVs :: Unify sig m => Global -> Global -> m ()
equateUVs gl1 gl2 = modify (\st -> st { unUVEqs = Map.fromList [(gl1, gl2), (gl2, gl1)] <> unUVEqs st })

bind2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
bind2 f act1 act2 = do
  x <- act1
  y <- act2
  f x y

unifyUnivs :: Unify sig m => Universe -> Universe -> m ()
unifyUnivs (SUniVar gl1) (SUniVar gl2) | gl1 == gl2 = pure ()
unifyUnivs s1@(SUniVar gl1) s2@(SUniVar gl2) = equateUVs gl1 gl2
unifyUnivs (SUniVar gl) s = putUniverseSol gl s
unifyUnivs s (SUniVar gl) = putUniverseSol gl s
unifyUnivs Meta Meta = pure ()
unifyUnivs Obj Obj = pure ()
unifyUnivs (Low l1) (Low l2) | l1 == l2 = pure ()
unifyUnivs _ _ = throwError ()

unifyRedexes :: Unify sig m => Redex -> Redex -> m ()
unifyRedexes (MetaFunElim lam1 arg1) (MetaFunElim lam2 arg2) = do
  unify' lam1 lam2
  unify' arg1 arg2
unifyRedexes (ObjFunElim lam1 arg1) (ObjFunElim lam2 arg2) = do
  unify' lam1 lam2
  unify' arg1 arg2
unifyRedexes (CodeCoreElim quote1) (CodeCoreElim quote2) = unify' quote1 quote2
unifyRedexes (CodeLowCTmElim quote1) (CodeLowCTmElim quote2) = unify' quote1 quote2
unifyRedexes (GlobalVar did1) (GlobalVar did2) | did1 == did2 = pure ()
unifyRedexes (TwoElim scr1 _ body11 body21) (TwoElim scr2 _ body12 body22) = do
  unify' scr1 scr2
  unify' body11 body12
  unify' body21 body22
unifyRedexes (SingElim term1) (SingElim term2) = unify' term1 term2
unifyRedexes (RecElim str1 name1) (RecElim str2 name2) | name1 == name2 =
  unify' str1 str2
unifyRedexes _ _ = throwError ()

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

-- unifyVCs :: Unify sig m => ValueCategory -> ValueCategory -> m ()
-- unifyVCs (VCUniVar gl1) (VCUniVar gl2) = equateUVs gl1 gl2
-- unifyVCs (VCUniVar gl) vc = putVCSol gl vc
-- unifyVCs vc (VCUniVar gl) = putVCSol gl vc
-- unifyVCs RVal RVal = pure ()
-- unifyVCs LVal LVal = pure ()
-- unifyVCs _ _ = throwError ()

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

unifyRigid :: Unify sig m => RigidTerm Term -> RigidTerm Term -> m ()
unifyRigid (MetaConstIntro did1) (MetaConstIntro did2) | did1 == did2 = pure ()
unifyRigid (ObjConstIntro did1) (ObjConstIntro did2) | did1 == did2 = pure ()
unifyRigid (CodeCoreType ty1) (CodeCoreType ty2) = unify' ty1 ty2
unifyRigid (CodeLowCTmType ty1) (CodeLowCTmType ty2) = unify' ty1 ty2
unifyRigid (CodeCoreIntro term1) (CodeCoreIntro term2) = unify' term1 term1
unifyRigid (CodeLowCTmIntro term1) (CodeLowCTmIntro term2) = unify' term1 term1
unifyRigid (CodeLowCStmtType ty1) (CodeLowCStmtType ty2) = unify' ty1 ty2
unifyRigid (CodeLowCStmtIntro stmt1) (CodeLowCStmtIntro stmt2) = unifyStmts stmt1 stmt2
unifyRigid (CPtrType ty1) (CPtrType ty2) = unify' ty1 ty2
unifyRigid CIntType CIntType = pure ()
unifyRigid CVoidType CVoidType = pure ()
unifyRigid (CFunType inTys1 outTy1) (CFunType inTys2 outTy2) = do
  traverse (uncurry unify') (zip inTys1 inTys2)
  unify' outTy1 outTy2
unifyRigid (CIntIntro x1) (CIntIntro x2) | x1 == x2 = pure ()
unifyRigid (COp op1) (COp op2) = unifyOps op1 op2
unifyRigid (CFunCall fn1 args1) (CFunCall fn2 args2) = do
  unify' fn1 fn2
  traverse_ (uncurry unify') (zip args1 args2)
unifyRigid (PropConstIntro did1) (PropConstIntro did2) | did1 == did2 = pure ()
unifyRigid (ImplType inTy1 outTy1) (ImplType inTy2 outTy2) = do
  unify' inTy1 inTy2
  unify' outTy1 outTy2
unifyRigid (ConjType lprj1 rprj1) (ConjType lprj2 rprj2) = do
  unify' lprj1 lprj2
  unify' rprj1 rprj2
unifyRigid (DisjType linj1 rinj1) (DisjType linj2 rinj2) = do
  unify' linj1 linj2
  unify' rinj1 rinj2
unifyRigid (ObjIdType x1 y1) (ObjIdType x2 y2) = do
  unify' x1 x2
  unify' y1 y2
unifyRigid (PropIdType x1 y1) (PropIdType x2 y2) = do
  unify' x1 x2
  unify' y1 y2
unifyRigid TwoIntro0 TwoIntro0 = pure ()
unifyRigid TwoIntro1 TwoIntro1 = pure ()
unifyRigid TwoType TwoType = pure ()
unifyRigid (ObjIdIntro x1) (ObjIdIntro x2) = unify' x1 x2
unifyRigid (AllType f1) (AllType f2) = unify' f1 f2
unifyRigid (SomeType f1) (SomeType f2) = unify' f1 f2
unifyRigid ElabError _ = pure ()
unifyRigid _ ElabError = pure ()
unifyRigid _ _ = throwError ()

unify' :: HasCallStack => Unify sig m => Term -> Term -> m ()
unify' (Neutral _ (UniVar gl1)) (Neutral _ (UniVar gl2)) = equateUVs gl1 gl2
unify' (Neutral prevSol (UniVar gl)) term = do
  prevSol <- force prevSol
  case prevSol of
    Just prevSol -> unify' prevSol term
    Nothing -> putTypeSol gl term
unify' term (Neutral prevSol (UniVar gl)) = do
  prevSol <- force prevSol
  case prevSol of
    Just prevSol -> unify' prevSol term
    Nothing -> putTypeSol gl term
unify' (Neutral term1 redex1) (Neutral term2 redex2) = catchError (unifyRedexes redex1 redex2) (\() -> go) where
  go :: Unify sig m => m ()
  go = do
    term1 <- force term1
    term2 <- force term2
    case (term1, term2) of
      (Just term1, Just term2) -> unify' term1 term2
      _ -> throwError ()
unify' (Neutral term1 _) term2 = do
  term1 <- force term1
  case term1 of
    Just term1 -> unify' term1 term2
    Nothing -> throwError ()
unify' term1 (Neutral term2 _) = do
  term2 <- force term2
  case term2 of
    Just term2 -> unify' term1 term2
    Nothing -> throwError ()
unify' (MetaFunType inTy1 outTy1) (MetaFunType inTy2 outTy2) = do
  unify' inTy1 inTy2
  bind2 unify' (evalClosure outTy1) (evalClosure outTy2)
unify' (MetaFunIntro body1) (MetaFunIntro body2) = bind2 unify' (evalClosure body1) (evalClosure body2)
unify' (ObjFunType inTy1 outTy1) (ObjFunType inTy2 outTy2) = do
  unify' inTy1 inTy2
  bind2 unify' (evalClosure outTy1) (evalClosure outTy2)
unify' (ObjFunIntro body1) (ObjFunIntro body2) = bind2 unify' (evalClosure body1) (evalClosure body2)
unify' (TypeType s1) (TypeType s2) = unifyUnivs s1 s2
unify' (LocalVar lvl1) (LocalVar lvl2) | lvl1 == lvl2 = pure ()
unify' (RecType fdTys1) (RecType fdTys2) =
  traverse_
    (\((name1, ty1), (name2, ty2)) -> do
      when (name1 /= name2) (throwError ())
      unify' ty1 ty2)
    (zip fdTys1 fdTys2)
unify' (RecIntro fds1) (RecIntro fds2) =
  traverse_
    (\((name1, fd1), (name2, fd2)) -> do
      when (name1 /= name2) (throwError ())
      unify' fd1 fd2)
    (zip fds1 fds2)
unify' (Rigid term1) (Rigid term2) = unifyRigid term1 term2
unify' _ _ = throwError ()

unify :: HasCallStack => Norm sig m => Term -> Term -> m (Maybe Substitution)
unify term1 term2 = do
  r <- runError @() . runState mempty $ unify' term1 term2
  case r of
    Right (subst, _) -> pure (Just subst)
    Left _ -> pure Nothing
