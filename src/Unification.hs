{-# LANGUAGE UndecidableInstances #-}
module Unification where

import Control.Effect.Reader
import Control.Carrier.Reader(runReader)
import Control.Effect.Error
import Control.Carrier.Error.Either(runError)
import Control.Effect.State
import Control.Carrier.State.Strict(runState)
import Syntax.Semantic
import Syntax.Core qualified as C
import Syntax.Common
import Normalization hiding(unUVEqs)
import Normalization qualified as Norm
import Data.Set(Set)
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
import Prelude hiding(zip, length, filter, elem)
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
  , Has (State Substitution) sig m
  , Has (Reader (Set Global)) sig m )

putTypeSolExp :: Unify sig m => Global -> Term -> m (Coercion sig m)
putTypeSolExp gl sol = do
  sols <- get
  case Map.lookup gl (unTypeSols sols) of
    Nothing -> do
      occurs mempty gl sol
      put (sols { unTypeSols = Map.insert gl sol (unTypeSols sols) })
      pure noop
    Just sol' -> unify' sol sol'

putTypeSolInf :: Unify sig m => Global -> Term -> m (Coercion sig m)
putTypeSolInf gl sol = do
  sols <- get
  case Map.lookup gl (unTypeSols sols) of
    Nothing -> do
      occurs mempty gl sol
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

withVisited :: Unify sig m => Global -> m a -> m a
withVisited gl act = do
  visited <- ask
  if Set.member gl visited then
    throwError ()
  else
    local (Set.insert gl) act

unifyRedexes :: Unify sig m => Redex -> Redex -> m ()
unifyRedexes (TextElimCat t11 t12) (TextElimCat t21 t22) = do
  unifyS' t11 t21
  unifyS' t12 t22
unifyRedexes (MetaFunElim lam1 arg1) (MetaFunElim lam2 arg2) = do
  unifyS' lam1 lam2
  unifyS' arg1 arg2
unifyRedexes (ObjFunElim lam1 arg1) (ObjFunElim lam2 arg2) = do
  unifyS' lam1 lam2
  unifyS' arg1 arg2
unifyRedexes (CodeObjElim quote1) (CodeObjElim quote2) =
  unifyS' quote1 quote2
unifyRedexes (CodeCElim quote1) (CodeCElim quote2) =
  unifyS' quote1 quote2
unifyRedexes (GlobalVar did1 _) (GlobalVar did2 _) =
  unifyS' did1 did2
unifyRedexes (TwoElim scr1 body11 body21) (TwoElim scr2 body12 body22) = do
  unifyS' scr1 scr2
  unifyS' body11 body12
  unifyS' body21 body22
unifyRedexes (SingElim term1) (SingElim term2) =
  unifyS' term1 term2
unifyRedexes (RecElim str1 name1) (RecElim str2 name2) | name1 == name2 =
  unifyS' str1 str2
unifyRedexes (UniVar gl1) (UniVar gl2) = equateUVs gl1 gl2
  -- putTypeSolInf gl1 (Neutral (uvRedex gl2) (UniVar gl2))
  -- putTypeSolExp gl2 (Neutral (uvRedex gl1) (UniVar gl1))
  -- pure ()
unifyRedexes (Declare univ1 name1 ty1 cont1) (Declare univ2 name2 ty2 cont2) | univ1 == univ2 = do
  unifyS' name1 name2
  unifyS' ty1 ty2
  unifyS' cont1 cont2
unifyRedexes (Define name1 def1 cont1) (Define name2 def2 cont2) = do
  unifyS' name1 name2
  unifyS' def1 def2
  unifyS' cont1 cont2
unifyRedexes _ _ = throwError ()

unifyRigid :: Unify sig m => RigidTerm Term -> RigidTerm Term -> m (Coercion sig m)
unifyRigid TextType TextType = pure noop
unifyRigid TextIntroNil TextIntroNil = pure noop
unifyRigid (TextIntroCons c1 t1) (TextIntroCons c2 t2) | c1 == c2 = do
  unifyS' t1 t2
  pure noop
unifyRigid (MetaConstIntro did1) (MetaConstIntro did2) | did1 == did2 =
  pure noop
unifyRigid (CodeObjType ty1) (CodeObjType ty2) = do
  unifyS' ty1 ty2
  pure noop
unifyRigid (CodeObjIntro term1) (CodeObjIntro term2) = do
  unifyS' term1 term2
  pure noop
unifyRigid (PropConstIntro did1) (PropConstIntro did2) | did1 == did2 = pure noop
unifyRigid (ImplType inTy1 outTy1) (ImplType inTy2 outTy2) = do
  unifyS' inTy1 inTy2
  unifyS' outTy1 outTy2
  pure noop
unifyRigid (ConjType lprj1 rprj1) (ConjType lprj2 rprj2) = do
  unifyS' lprj1 lprj2
  unifyS' rprj1 rprj2
  pure noop
unifyRigid (DisjType linj1 rinj1) (DisjType linj2 rinj2) = do
  unifyS' linj1 linj2
  unifyS' rinj1 rinj2
  pure noop
unifyRigid (ObjIdType x1 y1) (ObjIdType x2 y2) = do
  unifyS' x1 x2
  unifyS' y1 y2
  pure noop
unifyRigid (PropIdType x1 y1) (PropIdType x2 y2) = do
  unifyS' x1 x2
  unifyS' y1 y2
  pure noop
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
unifyRigid (NameType univ1 ty1) (NameType univ2 ty2)
  | univ1 == univ2
  = do
    unifyS' ty1 ty2
    pure noop
unifyRigid (NameIntro univ1 did1) (NameIntro univ2 did2)
  | univ1 == univ2 && did1 == did2
  = pure noop
unifyRigid ElabError _ = pure noop
unifyRigid _ ElabError = pure noop
unifyRigid term1 term2 = throwError ()

occurs :: Unify sig m => Set Id -> Global -> Term -> m ()
occurs vis gl term = case term of
  ObjFunType _ inTy outTy -> do
    occurs vis gl inTy
    evalClosure outTy >>= occurs vis gl
  ObjFunIntro body -> evalClosure body >>= occurs vis gl
  MetaFunType _ inTy outTy -> do
    occurs vis gl inTy
    evalClosure outTy >>= occurs vis gl
  MetaFunIntro body -> evalClosure body >>= occurs vis gl
  RecType tys ->
    void (traverse (\ty -> evalClosure ty >>= occurs vis gl) (fmap snd tys))
  RecIntro defs ->
    void (traverse (occurs vis gl) (fmap snd defs))
  LocalVar _ -> pure ()
  Rigid rterm -> void (traverse (occurs vis gl) rterm)
  Neutral _ (UniVar gl') -> do
    eq <- Map.lookup gl' . Norm.unUVEqs <$> ask
    if gl' == gl || eq == Just gl then
      throwError ()
    else
      pure ()
  Neutral term redex -> do
    term <- force term
    case term of
      Just term ->
        let
          vis' = case redex of
            GlobalVar (Rigid (NameIntro _ did)) _ -> Set.insert did vis
            _ -> vis
        in occurs vis gl term
      Nothing -> pure ()

unify' :: HasCallStack => Unify sig m => Term -> Term -> m (Coercion sig m)
unify' term1 term2 =
  simple term1 term2 `catchError` (\() -> complex term1 term2)
  where
    simple :: Unify sig m => Term -> Term -> m (Coercion sig m)
    simple (Rigid ElabError) _ = pure noop
    simple _ (Rigid ElabError) = pure noop
    simple nterm1@(Neutral term1 redex1) nterm2@(Neutral term2 redex2) =
      catchError (unifyRedexes redex1 redex2 *> pure noop) (\() -> go)
      where
        go :: Unify sig m => m (Coercion sig m)
        go = do
          term1 <- force term1
          term2 <- force term2
          case (term1, term2) of
            (Just term1, Just term2) -> unify' term1 term2
            _ -> throwError ()
    simple (MetaFunType pm1 inTy1 outTy1) (MetaFunType pm2 inTy2 outTy2)
      | pm1 == pm2
      = do
        unifyS' inTy1 inTy2
        bind2 unifyS' (evalClosure outTy1) (evalClosure outTy2)
        pure noop
    simple (MetaFunIntro body1) (MetaFunIntro body2) = do
      bind2 unifyS' (evalClosure body1) (evalClosure body2)
      pure noop
    simple (ObjFunType pm1 inTy1 outTy1) (ObjFunType pm2 inTy2 outTy2)
      | pm1 == pm2 || pm1 == DontCare || pm2 == DontCare
      = do
        coe1 <- unify' inTy1 inTy2
        coe2 <- bind2 unify' (evalClosure outTy1) (evalClosure outTy2)
        case (isNoop coe1, isNoop coe2) of
          (False, False) ->
            pure (liftCoe \e -> do
              arg <- applyCoe coe1 (C.LocalVar 0)
              C.ObjFunIntro <$> applyCoe coe2 (C.ObjFunElim e arg))
          (True, True) -> pure noop
    simple (ObjFunIntro body1) (ObjFunIntro body2) = do
      bind2 unifyS' (evalClosure body1) (evalClosure body2)
      pure noop
    simple (LocalVar lvl1) (LocalVar lvl2) | lvl1 == lvl2 = pure noop
    simple (RecType tys1) (RecType tys2) | length tys1 == length tys2 = do
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
    simple (RecIntro fds1) (RecIntro fds2) = do
      traverse_
        (\((name1, fd1), (name2, fd2)) -> do
          when (name1 /= name2) (throwError ())
          unifyS' fd1 fd2)
        (zip fds1 fds2)
      pure noop
    simple (Rigid term1) (Rigid term2) = do
      unifyRigid term1 term2
      pure noop
    simple _ _ = throwError ()

    complex :: Unify sig m => Term -> Term -> m (Coercion sig m)
    complex (Neutral term1 (GlobalVar _ True)) term2 = do
      term1 <- fromJust <$> force term1
      unify' term1 term2
    complex term1 (Neutral term2 (GlobalVar _ True)) = do
      term2 <- fromJust <$> force term2
      unify' term1 term2
    complex (viewObjFunElims -> Just (Neutral _ (UniVar gl), spine)) term =
      withVisited gl do
        sol <- solve C.ObjFunIntro spine term
        putTypeSolInf gl sol
    complex term (viewObjFunElims -> Just (Neutral _ (UniVar gl), spine)) =
      withVisited gl do
        sol <- solve C.ObjFunIntro spine term
        putTypeSolExp gl sol
    complex (viewMetaFunElims -> Just (Neutral _ (UniVar gl), spine)) term =
      withVisited gl do
        sol <- solve C.MetaFunIntro spine term
        putTypeSolInf gl sol
    complex term (viewMetaFunElims -> Just (Neutral _ (UniVar gl), spine)) =
      withVisited gl do
        sol <- solve C.MetaFunIntro spine term
        putTypeSolExp gl sol
    complex (Rigid (SingType _ term)) _ =
      pure (liftCoe \e -> do
        vE <- eval e
        unifyS' term vE
        pure (C.Rigid (C.SingIntro e)))
    complex ty1 (Rigid (SingType ty2 _)) =
      pure (liftCoe \e -> do
        unifyS' ty1 ty2
        pure (C.SingElim e))
    complex (Rigid (CodeObjType ty1)) ty2 =
      pure (liftCoe \e -> pure (C.Rigid (C.CodeObjIntro e)))
    complex ty1 (Rigid (CodeObjType ty2)) =
      pure (liftCoe \e -> pure (C.CodeObjElim e))
    complex (Neutral _ (CodeObjElim term1)) term2 =
      unify' term1 (Rigid (CodeObjIntro term2))
    complex term1 (Neutral _ (CodeObjElim term2)) =
      unify' (Rigid (CodeObjIntro term1)) term2
    complex (Neutral term1 _) term2 = do
      term1 <- force term1
      case term1 of
        Just term1 -> unify' term1 term2
        Nothing -> throwError ()
    complex term1 (Neutral term2 _) = do
      term2 <- force term2
      case term2 of
        Just term2 -> unify' term1 term2
        Nothing -> throwError ()
    complex term1 term2 = throwError ()

solve :: Unify sig m => (C.Term -> C.Term) -> Seq Term -> Term -> m Term
solve fun spine rhs = do
  vars <- localVars spine
  let
    vars' =
      Set.fromList .
      toList .
      filter (\lvl -> length (filter (== lvl) vars) == 1) $
      vars
  allowable mempty vars' rhs
  cRhs <- readback rhs
  eval (foldl' (\acc _ -> fun acc) cRhs spine)
  where
    localVars :: Unify sig m => Seq Term -> m (Seq Level)
    localVars Empty = pure mempty
    localVars (e :<| spine) = do
      vars <- localVars spine
      e <- unfold e
      case e of
        LocalVar lvl -> pure (lvl <| vars)
        _ -> pure vars

    allowable :: Unify sig m => Set Id -> Set Level -> Term -> m ()
    allowable vis vars (ObjFunType _ inTy outTy) = do
      allowable vis vars inTy
      l <- level
      evalClosure outTy >>= allowable vis (Set.insert l vars)
    allowable vis vars (MetaFunType _ inTy outTy) = do
      allowable vis vars inTy
      l <- level
      evalClosure outTy >>= allowable vis (Set.insert l vars)
    allowable vis vars (ObjFunIntro body) = do
      l <- level
      evalClosure body >>= allowable vis (Set.insert l vars)
    allowable vis vars (MetaFunIntro body) = do
      l <- level
      evalClosure body >>= allowable vis (Set.insert l vars)
    allowable vis vars (RecIntro defs) =
      traverse_ (\(_, def) -> allowable vis vars def) defs
    allowable vis vars (RecType tys) = do
      vTys <- evalFieldTypes Empty tys
      l <- level
      traverseWithIndex
        (\i (_, ty) ->
          allowable vis (Set.fromList [l .. l + fromIntegral i] <> vars) ty)
        vTys
      pure ()
    allowable vis vars (LocalVar lvl) =
      if Set.member lvl vars then
        pure ()
      else
        throwError ()
    allowable vis vars (Rigid rterm) = traverse_ (allowable vis vars) rterm
    allowable vis vars (Neutral term redex) = do
      term <- force term
      case term of
        Just term -> case redex of
          GlobalVar (Rigid (NameIntro _ did)) _ ->
            if Set.member did vis then
              pure ()
            else
              allowable (Set.insert did vis) vars term
          _ -> allowable vis vars term
        Nothing -> traverse_ (allowable vis vars) redex

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
  r <- runError @() . runReader (mempty :: Set Global) . runState mempty $ unify' term1 term2
  case r of
    Right (subst, Coe Nothing) -> pure (Just (subst, e))
    Right (subst1, Coe (Just coe)) -> do
      e' <- runError @() . runReader (mempty :: Set Global) . runState subst1 $ coe e
      case e' of
        Right (subst2, e') -> pure (Just (subst2 <> subst1, e'))
        Left _ -> pure Nothing
    Left _ -> pure Nothing

unifyR :: HasCallStack => Norm sig m => Term -> Term -> m (Maybe Substitution)
unifyR term1 term2 = do
  r <- runError @() . runReader (mempty :: Set Global) . runState mempty $ unify' term1 term2
  case r of
    Right (subst, Coe Nothing) -> pure (Just subst)
    Right (_, Coe (Just _)) -> pure Nothing
    Left _ -> pure Nothing
