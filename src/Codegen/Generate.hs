module Codegen.Generate where

import Syntax.STG qualified as L
import Syntax.Extra(IOOperation(..), RuntimeRep, Id(..))
import Control.Effect.State
import Control.Algebra
import Data.Text hiding(length, zip, map)
import Data.Set(size)
import Control.Monad
import Data.Foldable

type Type = Text
type Name = Text
type Statement = Text
data Procedure = Proc Type Name [(Type, Name)] [Statement]
type Term = Text

{-
struct type {
  unsigned char tag;
  struct type* data[];
};
-}

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
    [ "struct type* ty = malloc(sizeof(struct type) + sizeof(struct type*));"
    , "ty->tag = 0;"
    , "ty->data[0] = " <> gInTy <> ";" ]
  pure "ty"
genValue L.Unit = pure "0"
genValue L.UnitType = do
  addStmts
    [ "struct type* ty = malloc(sizeof(type));"
    , "ty->tag = 1;" ]
  pure "ty"
genValue (L.IOType ty) = do
  gTy <- genValue ty
  addStmts
    [ "void* ty = malloc(sizeof(type) + sizeof(void*));"
    , "ty->tag = 2;"
    , "ty->data[0] = " <> gTy <> ";" ]
  pure "ty"
genValue (L.Univ _) = do
  addStmts
    [ "void* ty = malloc(sizeof(type));"
    , "ty->tag = 3;" ]
  pure "ty"

genDecl :: Generate sig m => L.Declaration -> m ()
genDecl (L.Fun name vs params body) = do
  gParams <- traverse (\(L.Binding rep name) -> (, genId name) <$> genRep rep) params
  stmts <- scope do
    gBody <- genTerm body
    addStmt ("return " <> gBody <> ";")
    unStmts <$> get >>= pure
  addProc "void*" (genId name <> "_fun") gParams stmts -- FIXME: `void*`
  addStmts (
    [ "void* caps = malloc(sizeof(void*) * " <> (pack . show) (size vs + length params) ] <> -- FIXME: `void*`
    map (\(v, i) -> "caps[" <> (pack . show) i <> "] = " <> genId v <> ";") (zip (toList vs) ([0 .. size vs])) <>
    [ "struct closure clo;"
    , "clo.arity = " <> (pack . show) (length params) <> ";"
    , "clo.caps = caps;"
    , "clo.caps_size = " <> (pack . show) (size vs) <> ";"
    , "clo.ptr = &" <> genId name <> ";"
    , "void* " <> genId name <> " = malloc(sizeof(struct closure));"
    , "*" <> genId name <> " = clo;"])


scope :: Generate sig m => m a -> m a
scope act = do
  state <- get
  put (state { unStmts = [] })
  x <- act
  state' <- get
  put (state { unProcs = unProcs state' })
  pure x

addStmt :: Generate sig m => Statement -> m ()
addStmt stmt = do
  state <- get
  put (state { unStmts = unStmts state ++ [stmt] })

addStmts :: Generate sig m => [Statement] -> m ()
addStmts stmts = traverse addStmt stmts *> pure ()

addProc :: Generate sig m => Type -> Name -> [(Type, Name)] -> [Statement] -> m ()
addProc ty name bs stmts = do
  let proc = Proc ty name bs stmts
  state <- get
  put (state { unProcs = unProcs state ++ [proc] })

genRep :: Generate sig m => RuntimeRep -> m Type
genRep _ = pure "void*" -- FIXME

genId :: Id -> Term
genId (Id name) = "_" <> (pack . show $ name)
