{-# LANGUAGE LambdaCase #-}

module Core where

import Var
import {-# SOURCE #-} qualified Norm as N
import Control.Monad.Reader(Reader, ask)
import Data.Map(Map)
import Numeric.Natural

data BinderInfo = Abstract | Concrete
  deriving Show

-- type annotation
type Type = Term

data HoleName = HoleName Int
  deriving Show

data Id = Id Natural

data Namespace = Namespace (Map Id (Term, Term))

data Term
  = Var Index Type
  | TypeType0
  | TypeType1
  | FunIntro Term Type
  | FunType Term Term
  | FunElim Term Term
  | QuoteType Term
  | QuoteIntro Term Type
  | QuoteElim Term
  | FinType Natural
  | FinIntro Natural Type
  | FinElim Term [Term]
  | PairType Term Term
  | PairIntro Term Term Type
  | PairElim Term Term
  | Let Term Term Term
  | Meta Global Type
  | InsertedMeta [BinderInfo] Global Type
  | ElabError

-- shift :: Set Index -> Term -> Reader Int Term
-- shift bounds = \case
--   Var ix ty ->
--     if ix `member` bounds then
--       pure $ Var ix ty
--     else do
--       amt <- ask
--       pure $ Var (Index $ unIndex ix + amt) ty
--   TypeType -> pure TypeType
--   FunIntro body ty -> FunIntro <$> shift next body <*> shift bounds ty
--   FunType inTy outTy -> FunType <$> shift bounds inTy <*> shift next outTy
--   FunElim lam arg -> FunElim <$> shift bounds lam <*> shift bounds arg
--   Let def defTy body -> Let <$> shift bounds def <*> shift bounds defTy <*> shift next body
--   Meta gl ty -> Meta <$> pure gl <*> shift bounds ty
--   InsertedMeta bis gl ty -> InsertedMeta <$> pure bis <*> pure gl <*> shift bounds ty
--   ElabError -> pure ElabError
--   _ -> error "Unimplemented"
--   where
--     next :: Set Index
--     next = insert (Index 0) $ Data.Set.map (\ix -> Index $ unIndex ix + 1) bounds

instance Show Term where
  show = showTerm False

showTerm :: Bool -> Term -> String
showTerm showTys term = case term of
  Var ix ty ->
    if showTys then
      "(i" ++ show (unIndex ix) ++ " : " ++ show ty ++ ")"
    else
      "i" ++ show (unIndex ix)
  TypeType0 -> "U0"
  TypeType1 -> "U1"
  FunIntro body ty ->
    if showTys then
      "{" ++ show body ++ "; : " ++ show ty ++ "}"
    else
      "{" ++ show body ++ "}"
  FunType inTy outTy -> show inTy ++ " -> " ++ show outTy
  FunElim lam arg -> "(" ++ show lam ++ " @ " ++ show arg ++ ")"
  QuoteType innerTy -> "Quote " ++ show innerTy
  QuoteIntro inner _ -> "<" ++ show inner ++ ">"
  QuoteElim quote -> "[" ++ show quote ++ "]"
  FinType n -> "Fin" ++ show n
  FinIntro n _ -> "fin" ++ show n
  FinElim scr bs -> "case " ++ show scr ++ show (map show bs)
  Let def defTy body -> "let " ++ show def ++ " : " ++ show defTy ++ " in\n" ++ show body
  Meta gl ty ->
    if showTys then
      "(?" ++ show (unGlobal gl) ++ " : " ++ show ty ++ ")"
    else
      "?" ++ show (unGlobal gl)
  InsertedMeta bis gl ty ->
    if showTys then
      "(?" ++ show (unGlobal gl) ++ " : " ++ show ty ++ ";" ++ (show $ Prelude.map show bis) ++ ")"
    else
      "?" ++ show (unGlobal gl) ++ (show $ Prelude.map show bis) ++ ""
  ElabError -> "<error>"