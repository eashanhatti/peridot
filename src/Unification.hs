module Unification where

-- Heavily based upon [this implementation](https://github.com/jozefg/higher-order-unification)

import Control.Monad.Logic
import Control.Applicative
import Control.Effect.Lift(Lift)
import Control.Effect.Reader(ask)
import Control.Effect.State(State, get, put)
import Control.Algebra(Has)
import Control.Monad
import Syntax.Semantic
import Syntax.Core qualified as C
import Data.Map(Map)
import Data.Map qualified as Map
import Data.Set(Set)
import Data.Set qualified as Set
import Data.List(foldl', partition)
import Syntax.Variable
import Normalization
import Control.Monad.Extra

newtype UnifyState = UnifyState Global

type Unify sig m = (Has (Lift Logic) sig m, Has (State UnifyState) sig m, Norm sig m)
type Constraint = (Term, Term)
type Substitution = Map Global Term

freshUniVar :: Unify sig m => m Global
freshUniVar = do
  UnifyState gl <- get
  put (UnifyState (gl + 1))
  pure gl

uniVars :: Norm sig m => Term -> m (Set Global)
uniVars (FunType inTy outTy) = do
  vOutTy <- evalClosure outTy
  (<>) <$> uniVars inTy <*> (evalClosure outTy >>= uniVars)
uniVars (FunIntro body) = evalClosure body >>= uniVars
uniVars (DatatypeIntro _ args) = foldM (\acc arg -> (acc <>) <$> uniVars arg) mempty args
uniVars (TypeType _) = pure mempty
uniVars (FreeVar _) = pure mempty
uniVars (UniVar gl) = pure (Set.singleton gl)
uniVars (StuckFunElim lam arg) = (<>) <$> uniVars lam <*> uniVars arg

isClosed :: Norm sig m => Term -> m Bool
isClosed (FunType inTy outTy) = (&&) <$> isClosed inTy <*> (evalClosure outTy >>= isClosed)
isClosed (FunIntro body) = evalClosure body >>= isClosed
isClosed (DatatypeIntro _ args) = andM (map isClosed args)
isClosed (TypeType _) = pure True
isClosed (FreeVar _) = pure False
isClosed (UniVar _) = pure True
isClosed (StuckFunElim lam arg) = (&&) <$> isClosed lam <*> isClosed arg

isStuck :: Term -> Bool
isStuck (StuckFunElim _ _) = True
isStuck (UniVar _) = True
isStuck _ = False

simplify :: (Alternative m, Norm sig m) => Constraint -> m [Constraint]
simplify (e1, e2) | e1 == e2 = pure []
simplify (e1, e2)
  | (FreeVar lvl1, args1) <- viewApp e1
  , (FreeVar lvl2, args2) <- viewApp e2
  = do
    guard (lvl1 == lvl2 && length args1 == length args2)
    mconcat <$> mapM simplify (zip args1 args2)
simplify (FunIntro body1, FunIntro body2) = do
  vBody1 <- evalClosure body1
  vBody2 <- evalClosure body2
  pure [(vBody1, vBody2)]
simplify (FunType inTy1 outTy1, FunType inTy2 outTy2) = do
  vOutTy1 <- evalClosure outTy1
  vOutTy2 <- evalClosure outTy2
  pure [(inTy1, inTy2), (vOutTy1, vOutTy2)]
simplify c = pure [c]

tryFlexRigid :: (Norm sig1 m1, Unify sig2 m2) => Constraint -> m1 [m2 [Substitution]]
tryFlexRigid (e1, e2) = do
  uniVars1 <- uniVars e1
  uniVars2 <- uniVars e2
  case (viewApp e1, viewApp e2, uniVars1, uniVars2) of
    ((UniVar gl, args), (lam, _), _, Set.member gl -> True) -> pure (proj (length args) gl lam 0)
    ((lam, args), (UniVar gl, _), Set.member gl -> True, _) -> pure (proj (length args) gl lam 0)

proj :: Unify sig m => Int -> Global -> Term -> Int -> [m [Substitution]]
proj bvars gl lam nargs = genSubst bvars gl lam nargs : proj bvars gl lam (nargs + 1)

genSubst :: Unify sig m => Int -> Global -> Term -> Int -> m [Substitution]
genSubst bvars gl lam nargs = do
  let mkLam tm = foldr ($) tm (replicate bvars C.FunIntro)
  let saturateUV tm = foldl' C.FunElim tm (map (C.Var . Index) [0 .. fromIntegral (bvars - 1)])
  args <- map saturateUV . map C.UniVar <$> replicateM nargs freshUniVar
  lamIsClosed <- isClosed lam
  cLam <- readback lam
  let vars = map (C.Var . Index) [0 .. fromIntegral (bvars - 1)] ++ if lamIsClosed then [cLam] else []
  forM vars \var -> do
    sol <- eval (mkLam (foldl' C.FunElim var args))
    pure (Map.singleton gl sol)

repeatedlySimplify :: (Alternative m, Unify sig m) => [Constraint] -> m [Constraint]
repeatedlySimplify cs = do
  cs' <- mconcat <$> traverse simplify cs
  if cs' == cs then
    pure cs
  else
    repeatedlySimplify cs'

unify :: (Alternative m, MonadLogic m, Unify sig m) => Substitution -> [Constraint] -> m (Substitution, [Constraint])
unify subst cs = do
  (flexFlexes, flexRigids) <- partition isFlexFlex <$> repeatedlySimplify cs
  if null flexRigids then
    pure (subst, flexFlexes)
  else do
    substss <- tryFlexRigid (head flexRigids)
    trySubsts substss (flexRigids ++ flexFlexes)
  where
    isFlexFlex (e1, e2) = isStuck e1 && isStuck e2
    trySubsts [] cs = empty
    trySubsts (act:substss) cs = do
      substs <- act
      let these = foldr interleave empty [unify (Map.union subst' subst) cs | subst' <- substs]
      let those = trySubsts substss cs
      interleave these those