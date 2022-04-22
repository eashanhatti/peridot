module Elaboration.CStatement where

import Elaboration.Effect
import Syntax.Surface hiding(CStatement)
import Syntax.Core qualified as C
import Syntax.Common(Name(..), Language(..), CStatement)
import Syntax.Semantic qualified as N
import {-# SOURCE #-} Elaboration.Term qualified as EE
import Data.Maybe(fromMaybe)
import Data.Sequence

infer' :: forall sig m. Elab sig m => CStatementAst -> m (CStatement C.Term, Maybe N.Term, Maybe (Name, N.Term))
infer' (CStmtAst (Block stmts)) = do
  (cStmt, retTy) <- go stmts
  pure (cStmt, retTy, Nothing)
  where
    go :: Elab sig m => Seq CStatementAst -> m (CStatement C.Term, Maybe N.Term)
    go (stmt :<| Empty) = do
      (cStmt, retTy, _) <- infer' stmt
      pure (cStmt, retTy)
    go (stmt :<| stmts) = do
      (cStmt, retTy, binding) <- infer' stmt
      let
        act = do
          (cStmts, retTy') <- go stmts
          unifyRetTys retTy retTy'
          pure (C.Block cStmt cStmts, pickMaybe retTy retTy')
      case binding of
        Just (name, ty) -> bindLocal name ty act
        Nothing -> act
infer' (CStmtAst (If cond trueBody falseBody)) = do
  cCond <- EE.check cond N.CIntType
  (cTrueBody, retTy1, _) <- infer' trueBody
  (cFalseBody, retTy2, _) <- infer' falseBody
  unifyRetTys retTy1 retTy2
  pure (C.If cCond cTrueBody cFalseBody, pickMaybe retTy1 retTy2, Nothing)
infer' (CStmtAst (VarDecl (NameAst name) ty)) = do
  cTy <- EE.check ty (N.TypeType (N.Low C))
  vTy <- eval cTy
  pure (C.VarDecl cTy, Nothing, Just (name, vTy))
infer' (CStmtAst (Assign var val)) = do
  ty <- freshTypeUV
  cVar <- EE.check var (N.CValType N.LVal ty)
  cVal <- EE.check val (N.CValType N.RVal ty)
  pure (C.Assign cVar cVal, Nothing, Nothing)
infer' (CStmtAst (Return Nothing)) = pure (C.Return Nothing, Nothing, Nothing)
infer' (CStmtAst (Return (Just term))) = do
  (cTerm, ty) <- EE.infer term
  pure (C.Return (Just cTerm), Just ty, Nothing)
infer' (CStmtAst (SpliceLowCStmt quote)) = do
  ty <- freshTypeUV
  cQuote <- EE.check quote (N.CodeLowCStmtType ty)
  ty <- readback ty >>= eval
  case ty of
    N.CValType N.RVal N.CVoidType -> pure (C.CodeLowCStmtElim cQuote, Nothing, Nothing)
    _ -> pure (C.CodeLowCStmtElim cQuote, Just ty, Nothing)

infer :: Elab sig m => CStatementAst -> m (CStatement C.Term, N.Term)
infer stmt = do
  (cStmt, retTy, _) <- infer' stmt
  pure (cStmt, fromMaybe (N.CValType N.RVal N.CVoidType) retTy)

unifyRetTys :: Elab sig m => Maybe N.Term -> Maybe N.Term -> m ()
unifyRetTys (Just ty1) (Just ty2) = unify ty1 ty2
unifyRetTys _ _ = pure ()

pickMaybe (Just x) (Just _) = Just x
pickMaybe (Just x) Nothing = Just x
pickMaybe Nothing (Just y) = Just y
pickMaybe Nothing Nothing = Nothing
