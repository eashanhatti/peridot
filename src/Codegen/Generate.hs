module Codegen.Generate where

import Syntax.STG qualified as L
import Syntax.Extra(IOOperation(..), RuntimeRep, Id(..))
import Control.Effect.State
import Control.Algebra
import Data.Text

type Type = Text
type Name = Text
type Statement = Text
data Procedure = Name [(Type, Name)] [Statement] Type
type Term = Text

data GenerateState = GenerateState
  { unProcs :: [Procedure]
  , unStmts :: [Statement] }

type Generate sig m = Has (State GenerateState) sig m

genTerm :: Generate sig m => L.Term -> m Term
genTerm (L.App lam args) = undefined
genTerm (L.Letrec decls body) = do
  traverse genDecl decls
  genTerm body
genTerm (L.Let bs body) = do
  traverse genLetBound bs
  genTerm body
genTerm (L.DoIO op body) = do
  genIOOp op
  genTerm body
genTerm (L.Val val) = genValue val

genLetBound :: Generate sig m => (L.Binding, L.Term) -> m ()
genLetBound (L.Binding rep name, term) = do
  gTerm <- genTerm term
  gRep <- genRep rep
  addStmt (gRep <> " " <> genId name <> " = " <> gTerm <> ";")

genIOOp :: Generate sig m => IOOperation -> m ()
genIOOp (PutChar c) = addStmt ("putchar(" <> singleton c <> ");")

genValue :: Generate sig m => L.Value -> m Term
genValue (L.Var name) = pure (genId name)
genValue (L.Arrow inTy) = do
  gInTy <- genValue inTy
  addStmts
    [ "void* ty = malloc(sizeof(void*) * 2);"
    , "ty[0] = 0;"
    , "ty[1] = " <> gInTy <> ";" ]
  pure "ty"
genValue L.Unit = pure "0"
genValue L.UnitType = do
  addStmts
    [ "void* ty = malloc(sizeof(void*));"
    , "ty[0] = 1;" ]
  pure "ty"
genValue (L.IOType ty) = do
  gTy <- genValue ty
  addStmts
    [ "void* ty = malloc(sizeof(void*) * 2);"
    , "ty[0] = 2;"
    , "ty[1] = " <> gTy <> ";" ]
  pure "ty"
genValue (L.Univ _) = do
  addStmts
    [ "void* ty = malloc(sizeof(void*));"
    , "ty[0] = 3;" ]
  pure "ty"

genDecl :: Generate sig m => L.Declaration -> m ()
genDecl (L.Fun name vs params body) = do


addStmt :: Generate sig m => Statement -> m ()
addStmt stmt = do
  state <- get
  put (state { unStmts = unStmts state ++ [stmt] })

addStmts :: Generate sig m => [Statement] -> m ()
addStmts stmts = traverse addStmt stmts *> pure ()

addProc :: Generate sig

genRep :: Generate sig m => RuntimeRep -> m Type
genRep = undefined

genId :: Id -> Term
genId (Id name) = pack . show $ name
