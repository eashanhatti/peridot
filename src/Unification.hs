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
  , unUVEqs :: Map Global Global }
  deriving (Show)

instance Semigroup Substitution where
  Subst ts1 eqs1 <> Subst ts2 eqs2 =
    Subst (ts1 <> ts2) (eqs1 <> eqs2)

instance Monoid Substitution where
  mempty = Subst mempty mempty

type Unify sig m =
  ( Norm sig m
  , Has (Error ()) sig m
  , Has (State Substitution) sig m )

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

equateUVs :: Unify sig m => Global -> Global -> m ()
equateUVs gl1 gl2 =
  modify (\st -> st
    { unUVEqs = Map.fromList [(gl1, gl2), (gl2, gl1)] <> unUVEqs st })

bind2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
bind2 f act1 act2 = do
  x <- act1
  y <- act2
  f x y

unifyRedexes :: Unify sig m => Redex -> Redex -> m ()
unifyRedexes (MetaFunElim lam1 arg1) (MetaFunElim lam2 arg2) = do
  unifyS' lam1 lam2
  unifyS' arg1 arg2
unifyRedexes (ObjFunElim lam1 arg1) (ObjFunElim lam2 arg2) = do
  unifyS' lam1 lam2
  unifyS' arg1 arg2
unifyRedexes (CodeCoreElim quote1) (CodeCoreElim quote2) =
  unifyS' quote1 quote2
unifyRedexes (GlobalVar did1) (GlobalVar did2) | did1 == did2 = pure ()
unifyRedexes (TwoElim scr1 body11 body21) (TwoElim scr2 body12 body22) = do
  unifyS' scr1 scr2
  unifyS' body11 body12
  unifyS' body21 body22
unifyRedexes (SingElim term1) (SingElim term2) =
  unifyS' term1 term2
unifyRedexes (RecElim str1 name1) (RecElim str2 name2) | name1 == name2 =
  unifyS' str1 str2
unifyRedexes _ _ = throwError ()

unifyRigid :: Unify sig m => RigidTerm Term -> RigidTerm Term -> m (Coercion sig m)
unifyRigid (MetaConstIntro did1) (MetaConstIntro did2) | did1 == did2 = pure noop
unifyRigid (ObjConstIntro did1) (ObjConstIntro did2) | did1 == did2 = pure noop
unifyRigid (CodeCoreType ty1) (CodeCoreType ty2) = unify' ty1 ty2
unifyRigid (CodeCoreIntro term1) (CodeCoreIntro term2) = do
  unifyS' term1 term1
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
unifyRigid (SingType _ term1) (SingType _ term2) = do
  unifyS' term1 term2
  pure noop
unifyRigid (SingIntro term1) (SingIntro term2) = do
  unifyS' term1 term2
  pure noop
unifyRigid (TypeType u1) (TypeType u2) | u1 == u2 = pure noop
unifyRigid ElabError _ = pure noop
unifyRigid _ ElabError = pure noop
unifyRigid term1 term2 = throwError ()

unify' :: HasCallStack => Unify sig m => Term -> Term -> m (Coercion sig m)
unify' (Rigid ElabError) _ = pure noop
unify' _ (Rigid ElabError) = pure noop
unify' (Neutral sol1 (UniVar gl1)) (Neutral sol2 (UniVar gl2)) = do
  sol1 <- force sol1
  sol2 <- force sol2
  case (sol1, sol2) of
    (Just sol1, Just sol2) -> unify' sol1 sol2
    (Just sol1, Nothing) -> putTypeSolInf gl2 sol1
    (Nothing, Just sol2) -> putTypeSolExp gl1 sol2
    (Nothing, Nothing) -> equateUVs gl1 gl2 *> pure noop
unify' (Neutral prevSol (UniVar gl)) term = do
  prevSol <- force prevSol
  case prevSol of
    Just prevSol -> unify' prevSol term
    Nothing -> putTypeSolInf gl term
unify' term (Neutral prevSol (UniVar gl)) = do
  prevSol <- force prevSol
  case prevSol of
    Just prevSol -> unify' term prevSol
    Nothing -> putTypeSolExp gl term
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
unify' (MetaFunType pm1 inTy1 outTy1) (MetaFunType pm2 inTy2 outTy2)
  | pm1 == pm2
  = do
    unifyS' inTy1 inTy2
    bind2 unifyS' (evalClosure outTy1) (evalClosure outTy2)
    pure noop
unify' (MetaFunIntro body1) (MetaFunIntro body2) = do
  bind2 unifyS' (evalClosure body1) (evalClosure body2)
  pure noop
unify' (ObjFunType pm1 inTy1 outTy1) (ObjFunType pm2 inTy2 outTy2)
  | pm1 == pm2
  = do
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
unify' (Rigid (SingType _ term)) _ =
  pure (liftCoe \e -> do
    vE <- eval e
    unifyS' term vE
    pure (C.Rigid (C.SingIntro e)))
unify' ty1 (Rigid (SingType ty2 _)) =
  pure (liftCoe \e -> do
    unifyS' ty1 ty2
    pure (C.SingElim e))
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
