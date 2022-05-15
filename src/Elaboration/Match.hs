module Elaboration.Match where

import Data.Sequence
import Elaboration.Effect
import Data.Map qualified as Map
import Syntax.Surface
import Syntax.Common
import Syntax.Semantic qualified as N
import Syntax.Core qualified as C
import Normalization
import Extra

data ConstraintPattern
  = CPCon Global Id (Seq ConstraintPattern)
  | CPBind Global

data PDClause = PDClse (Seq (ConstraintPattern, PatternAst)) PatternAst TermAst

check :: Elab sig m => Seq ClauseAst -> N.Term -> m C.Term
check cls goal = check' goal cls'
  where
    cls' = fmap
      (\(ClseAst (Clse pat body)) -> PDClse Empty pat body)
      cls

check' :: Elab sig m => N.Term -> Seq PDClause -> m C.Term
check' (N.MetaFunElims (N.Rigid (N.ObjConstIntro did)) args) _ = undefined
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

stripAppPat :: Seq PDClause -> Maybe (Seq (Global -> PDClause))
stripAppPat pcs = allJustOrNothing (fmap go pcs) where
  go (PDClse cs (PatAst (PApp (p :<| ps))) body) =
    Just (\gl -> PDClse ((CPBind gl, p) <| cs) (PatAst (PApp ps)) body)
  go _ = Nothing
