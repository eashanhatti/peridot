{-# LANGUAGE LambdaCase #-}

module Core where

import Var
import {-# SOURCE #-} qualified Norm as N
import Control.Monad.Reader(Reader, ask)
import Data.Map(Map)
import Data.Set(Set)
import Numeric.Natural

data BinderInfo = Abstract | Concrete
  deriving (Show, Eq)

-- type annotation
type Type = Term

data HoleName = HoleName Int
  deriving (Show, Eq)

-- data ItemAttrib = Opaque

data Program = Program [Item]
  deriving Show

data Item
  = TermDef Id Term
  | IndDef Id Term
  | ConDef Id Term
  deriving Show

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
  | IndType Id
  | IndIntro Id Natural [Term] Type
  -- | Let Term Term Term
  | Letrec [Term] Term
  | Meta Global Type
  | InsertedMeta [BinderInfo] Global Type
  | ElabError
  deriving Eq

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
  -- Let def defTy body -> "let " ++ show def ++ " : " ++ show defTy ++ " in\n" ++ show body
  Letrec defs body -> "letrec " ++ show defs ++ " in " ++ show body
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