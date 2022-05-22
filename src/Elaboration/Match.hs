module Elaboration.Match where

import Control.Effect.Reader
import Control.Effect.Error
import Data.Sequence
import Elaboration.Effect
import Data.Map qualified as Map
import Syntax.Surface
import Syntax.Common
import Syntax.Semantic qualified as N
import Syntax.Core qualified as C
import Normalization
import Extra
import Control.Monad
import Prelude hiding(filter, concatMap, unzip)

data ConstraintPattern
  = CPCon Id (Seq ConstraintPattern)
  | CPBind Global

type BoundVar = (NameAst, N.Term)

type Constraint = (ConstraintPattern, PatternAst)

data PDClause = PDClse (Seq Constraint) PatternAst TermAst (Seq BoundVar)

check :: Elab sig m => Seq ClauseAst -> N.Term -> m C.Term
check cls goal = check' goal cls'
  where
    cls' = fmap
      (\(ClseAst (Clse pat body)) -> PDClse Empty pat body mempty)
      cls

check' :: Elab sig m => N.Term -> Seq PDClause -> m C.Term
check' (N.MetaFunElims (N.Rigid (N.ObjConstIntro did)) args) _ = do
  constrs <- Map.lookup did . unConstrs <$> ask
  undefined
check' (N.ObjFunType inTy outTy) cls = do
  let cls' = stripAppPat cls
  case cls' of
    Just cls' -> do
      cls' <- traverse (<$> freshBareTypeUV) cls'
      C.ObjFunIntro <$> (evalClosure outTy >>= flip check' cls')
    Nothing -> fst <$> errorTerm Todo
check' (N.Neutral ty _) cls = do
  ty <- force ty
  case ty of
    Just ty -> check' ty cls
    Nothing -> fst <$> errorTerm Todo

processCPs :: Elab sig m => PDClause -> m PDClause
processCPs (PDClse cs pat body subst) = do
  (cs', subst') <-
    unzip <$>
    (complete <=<
    concatMapM simplify $
    cs)
  pure (PDClse cs' pat body (subst <> subst'))
  where
    simplify :: Elab sig m => Constraint -> m (Seq Constraint)
    simplify (CPCon did cps, PatAst (PCon name ps)) = do
      undefined
    simplify c = pure (singleton c)

    complete :: Elab sig m => Seq Constraint -> m (Seq (Constraint, BoundVar))
    complete = undefined

stripAppPat :: Seq PDClause -> Maybe (Seq (Global -> PDClause))
stripAppPat pcs = allJustOrNothing (fmap go pcs) where
  go (PDClse cs (PatAst (PApp (p :<| ps))) body subst) =
    Just (\gl -> PDClse ((CPBind gl, p) <| cs) (PatAst (PApp ps)) body subst)
  go _ = Nothing
