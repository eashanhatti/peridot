{-# LANGUAGE UndecidableInstances #-}
module Unification where

import Control.Effect.Error
import Control.Carrier.Error.Either(runError)
import Control.Effect.State
import Control.Carrier.State.Strict(runState)
import Syntax.Semantic
import Syntax.Core qualified as C
import Syntax.Common
import Normalization hiding(unUVEqs)
import Data.Set qualified as Set
import Data.Map(Map)
import Data.Map qualified as Map
import Control.Monad
import Data.Foldable hiding(length)
import GHC.Stack
import Debug.Trace
import Data.Maybe
import Data.Sequence
import Control.Applicative
import Prelude hiding(zip, length)
import Extra

-- coerce term of inferred type to term of expected type
newtype Coercion sig m =
  Coe (Unify sig m => Maybe (C.Term -> m C.Term))

instance Unify sig m => Show (Coercion sig m) where
  show (Coe Nothing) = "Noop"
  show _ = "SomeCoe"

noop :: Coercion sig m
noop = Coe Nothing

liftCoe :: Norm sig m => (C.Term -> m C.Term) -> Coercion sig m
liftCoe coe = Coe (Just coe)

applyCoe :: Unify sig m => Coercion sig m -> C.Term -> m C.Term
applyCoe (Coe (Just coe)) term = coe term
applyCoe (Coe Nothing) term = pure term

isNoop :: Unify sig m => Coercion sig m -> Bool
isNoop (Coe Nothing) = True
isNoop _ = False

data Substitution = Subst
  { unTypeSols :: Map Global Term
  , unUnivSols :: Map Global Universe
  -- , unVCSols :: Map Global ValueCategory
  , unUVEqs :: Map Global Global }
  deriving (Show)

instance Semigroup Substitution where
  Subst ts1 ss1 {-vcs1-} eqs1 <> Subst ts2 ss2 {-vcs2-} eqs2 =
    Subst (ts1 <> ts2) (ss1 <> ss2) {-(vcs1 <> vcs2)-} (eqs1 <> eqs2)

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

putTypeSolExp :: Unify sig m => Global -> Term -> m (Coercion sig m)
putTypeSolExp gl sol = do
  sols <- get
  case Map.lookup gl (unTypeSols sols) of
    Nothing -> do
      put (sols { unTypeSols = Map.insert gl sol (unTypeSols sols) })
      pure noop
    Just sol' -> unify' sol sol'

putTypeSolInf :: Unify sig m => Global -> Term -> m (Coercion sig m)
putTypeSolInf gl sol = do
  sols <- get
  case Map.lookup gl (unTypeSols sols) of
    Nothing -> do
      put (sols { unTypeSols = Map.insert gl sol (unTypeSols sols) })
      pure noop
    Just sol' -> unify' sol' sol

-- putVCSol :: Unify sig m => Global -> ValueCategory -> m ()
-- putVCSol gl sol = do
--   sols <- get
--   case Map.lookup gl (unVCSols sols) of
--     Nothing -> put (sols { unVCSols = Map.insert gl sol (unVCSols sols) })
--     Just sol' -> pure ()

equateUVs :: Unify sig m => Global -> Global -> m ()
equateUVs gl1 gl2 =
  modify (\st -> st
    { unUVEqs = Map.fromList [(gl1, gl2), (gl2, gl1)] <> unUVEqs st })

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
  unifyS' lam1 lam2
  unifyS' arg1 arg2
unifyRedexes (ObjFunElim lam1 arg1) (ObjFunElim lam2 arg2) = do
  unifyS' lam1 lam2
  unifyS' arg1 arg2
unifyRedexes (CodeCoreElim quote1) (CodeCoreElim quote2) =
  unifyS' quote1 quote2
unifyRedexes (CodeLowCTmElim quote1) (CodeLowCTmElim quote2) =
  unifyS' quote1 quote2
unifyRedexes (GlobalVar did1) (GlobalVar did2) | did1 == did2 = pure ()
unifyRedexes (TwoElim scr1 _ body11 body21) (TwoElim scr2 _ body12 body22) = do
  unifyS' scr1 scr2
  unifyS' body11 body12
  unifyS' body21 body22
unifyRedexes (SingElim term1) (SingElim term2) =
  unifyS' term1 term2
unifyRedexes (RecElim str1 name1) (RecElim str2 name2) | name1 == name2 =
  unifyS' str1 str2
unifyRedexes _ _ = throwError ()

unifyStmts :: Unify sig m => CStatement Term -> CStatement Term -> m ()
unifyStmts (VarDecl ty1) (VarDecl ty2) = unifyS' ty1 ty2
unifyStmts (Assign var1 val1) (Assign var2 val2) = do
  unifyS' var1 var2
  unifyS' val1 val2
unifyStmts (If cond1 trueBody1 falseBody1) (If cond2 trueBody2 falseBody2) = do
  unifyS' cond1 cond2
  unifyStmts trueBody1 trueBody2
  unifyStmts falseBody1 falseBody2
unifyStmts (Block lstmt1 rstmt1) (Block lstmt2 rstmt2) = do
  unifyStmts lstmt1 lstmt2
  unifyStmts rstmt1 rstmt2
unifyStmts (Return (Just val1)) (Return (Just val2)) = unifyS' val1 val2
unifyStmts (Return Nothing) (Return Nothing) = pure ()
unifyStmts (CodeLowCStmtElim quote1) (CodeLowCStmtElim quote2) = unifyS' quote1 quote2

-- unifyVCs :: Unify sig m => ValueCategory -> ValueCategory -> m ()
-- unifyVCs (VCUniVar gl1) (VCUniVar gl2) = equateUVs gl1 gl2
-- unifyVCs (VCUniVar gl) vc = putVCSol gl vc
-- unifyVCs vc (VCUniVar gl) = putVCSol gl vc
-- unifyVCs RVal RVal = pure ()
-- unifyVCs LVal LVal = pure ()
-- unifyVCs _ _ = throwError ()

unifyOps :: Unify sig m => COp Term -> COp Term -> m ()
unifyOps (Ref term1) (Ref term2) = unifyS' term1 term2
unifyOps (Deref term1) (Deref term2) = unifyS' term1 term2
unifyOps (Add x1 y1) (Add x2 y2) = do
  unifyS' x1 x2
  unifyS' y1 y2
unifyOps (Sub x1 y1) (Sub x2 y2) = do
  unifyS' x1 x2
  unifyS' y1 y2
unifyOps (Less x1 y1) (Less x2 y2) = do
  unifyS' x1 x2
  unifyS' y1 y2
unifyOps (Grtr x1 y1) (Grtr x2 y2) = do
  unifyS' x1 x2
  unifyS' y1 y2
unifyOps (Eql x1 y1) (Eql x2 y2) = do
  unifyS' x1 x2
  unifyS' y1 y2

unifyRigid :: Unify sig m => RigidTerm Term -> RigidTerm Term -> m (Coercion sig m)
unifyRigid (MetaConstIntro did1) (MetaConstIntro did2) | did1 == did2 = pure noop
unifyRigid (ObjConstIntro did1) (ObjConstIntro did2) | did1 == did2 = pure noop
unifyRigid (CodeCoreType ty1) (CodeCoreType ty2) = unify' ty1 ty2
unifyRigid (CodeLowCTmType ty1) (CodeLowCTmType ty2) = unify' ty1 ty2
unifyRigid (CodeCoreIntro term1) (CodeCoreIntro term2) = do
  unifyS' term1 term1
  pure noop
unifyRigid (CodeLowCTmIntro term1) (CodeLowCTmIntro term2) = do
  unifyS' term1 term1
  pure noop
unifyRigid (CodeLowCStmtType ty1) (CodeLowCStmtType ty2) = unify' ty1 ty2
unifyRigid (CodeLowCStmtIntro stmt1) (CodeLowCStmtIntro stmt2) = do
  unifyStmts stmt1 stmt2
  pure noop
unifyRigid (CPtrType ty1) (CPtrType ty2) = unify' ty1 ty2
unifyRigid CIntType CIntType = pure noop
unifyRigid CVoidType CVoidType = pure noop
unifyRigid (CFunType inTys1 outTy1) (CFunType inTys2 outTy2) = do
  traverse (uncurry unify') (zip inTys1 inTys2)
  unify' outTy1 outTy2
unifyRigid (CIntIntro x1) (CIntIntro x2) | x1 == x2 = pure noop
unifyRigid (COp op1) (COp op2) = do
  unifyOps op1 op2
  pure noop
unifyRigid (CFunCall fn1 args1) (CFunCall fn2 args2) = do
  unifyS' fn1 fn2
  traverse_ (uncurry unifyS') (zip args1 args2)
  pure noop
unifyRigid (PropConstIntro did1) (PropConstIntro did2) | did1 == did2 = pure noop
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
unifyRigid TwoIntro0 TwoIntro0 = pure noop
unifyRigid TwoIntro1 TwoIntro1 = pure noop
unifyRigid TwoType TwoType = pure noop
unifyRigid (ObjIdIntro x1) (ObjIdIntro x2) = do
  unifyS' x1 x2
  pure noop
unifyRigid (AllType f1) (AllType f2) = unify' f1 f2
unifyRigid (SomeType f1) (SomeType f2) = unify' f1 f2
unifyRigid (SingType term1) (SingType term2) = do
  unifyS' term1 term2
  pure noop
unifyRigid (SingIntro term1) (SingIntro term2) = do
  unifyS' term1 term2
  pure noop
unifyRigid ElabError _ = pure noop
unifyRigid _ ElabError = pure noop
unifyRigid term1 term2 = throwError ()

unify' :: HasCallStack => Unify sig m => Term -> Term -> m (Coercion sig m)
unify' (Rigid ElabError) _ = pure noop
unify' _ (Rigid ElabError) = pure noop
unify' (Neutral _ (UniVar gl1)) (Neutral _ (UniVar gl2)) = do
  equateUVs gl1 gl2
  pure noop
unify' (Neutral _ (UniVar gl)) term = putTypeSolInf gl term
unify' term (Neutral _ (UniVar gl)) = putTypeSolExp gl term
unify' (Neutral term1 redex1) (Neutral term2 redex2) =
  catchError (unifyRedexes redex1 redex2 *> pure noop) (\() -> go)
  where
    go :: Unify sig m => m (Coercion sig m)
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
  unifyS' inTy1 inTy2
  bind2 unifyS' (evalClosure outTy1) (evalClosure outTy2)
  pure noop
unify' (MetaFunIntro body1) (MetaFunIntro body2) = do
  bind2 unifyS' (evalClosure body1) (evalClosure body2)
  pure noop
unify' (ObjFunType inTy1 outTy1) (ObjFunType inTy2 outTy2) = do
  coe1 <- unify' inTy1 inTy2
  coe2 <- bind2 unify' (evalClosure outTy1) (evalClosure outTy2)
  case (isNoop coe1, isNoop coe2) of
    (False, False) ->
      pure (liftCoe \e -> do
        arg <- applyCoe coe1 (C.LocalVar 0)
        C.ObjFunIntro <$> applyCoe coe2 (C.ObjFunElim e arg))
    (True, True) -> pure noop
unify' (ObjFunIntro body1) (ObjFunIntro body2) = do
  bind2 unifyS' (evalClosure body1) (evalClosure body2)
  pure noop
unify' (TypeType s1) (TypeType s2) = do
  unifyUnivs s1 s2
  pure noop
unify' (LocalVar lvl1) (LocalVar lvl2) | lvl1 == lvl2 = pure noop
unify' (RecType tys1) (RecType tys2) | length tys1 == length tys2 = do
  coes <- go Empty (zip tys1 tys2)
  if all isNoop coes then
    pure noop
  else
    pure (liftCoe \e ->
      C.RecIntro <$>
        traverse
          (\(fd, coe) -> do
            (fd ,) <$> applyCoe coe (C.RecElim e fd))
          (zip (fmap fst tys1) coes))
  where
    go ::
      Unify sig m =>
      Seq Term ->
      Seq ((Field, Closure), (Field, Closure)) ->
      m (Seq (Coercion sig m))
    go _ Empty = pure Empty
    go defs (((fd1, ty1), (fd2, ty2)) :<| tys) = do
      when (fd1 /= fd2) (throwError ())
      vTy1 <- appClosureN ty1 defs
      vTy2 <- appClosureN ty2 defs
      coe <- unify' vTy1 vTy2
      l <- level
      (coe <|) <$> bind (go (LocalVar l <| defs) tys)
unify' (RecIntro fds1) (RecIntro fds2) = do
  traverse_
    (\((name1, fd1), (name2, fd2)) -> do
      when (name1 /= name2) (throwError ())
      unifyS' fd1 fd2)
    (zip fds1 fds2)
  pure noop
unify' (Rigid term1) (Rigid term2) = unifyRigid term1 term2
unify' (Rigid (SingType term)) _ =
  pure (liftCoe \e -> do
    vE <- eval e
    unifyS' term vE
    pure (C.Rigid (C.SingIntro e)))
unify' term1 term2 = throwError ()

unifyS' :: HasCallStack => Unify sig m => Term -> Term -> m ()
unifyS' term1 term2 = do
  r <- unify' term1 term2
  case r of
    Coe (Just _) -> throwError ()
    Coe Nothing -> pure ()

unify ::
  HasCallStack => Norm sig m =>
  C.Term ->
  Term ->
  Term ->
  m (Maybe (Substitution, C.Term))
unify e term1 term2 = do
  r <- runError @() . runState mempty $ unify' term1 term2
  case r of
    Right (subst, Coe Nothing) -> pure (Just (subst, e))
    Right (subst1, Coe (Just coe)) -> do
      e' <- runError @() . runState subst1 $ coe e
      case e' of
        Right (subst2, e') -> pure (Just (subst2 <> subst1, e'))
        Left _ -> pure Nothing
    Left _ -> pure Nothing

unifyR :: HasCallStack => Norm sig m => Term -> Term -> m (Maybe Substitution)
unifyR term1 term2 = do
  r <- runError @() . runState mempty $ unify' term1 term2
  case r of
    Right (subst, Coe Nothing) -> pure (Just subst)
    Right (_, Coe (Just _)) -> pure Nothing
    Left _ -> pure Nothing
