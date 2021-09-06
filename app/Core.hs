{-# LANGUAGE LambdaCase #-}

module Core where

import Var
import {-# SOURCE #-} Norm(Value)
import Control.Monad.Reader(Reader, ask)
import Data.Set

data BinderInfo = Abstract | Concrete
  deriving Show

-- type annotation
type Type = Term

data HoleName = HoleName Int
  deriving Show

data Stage = R | C | T | StageMeta Global
  deriving (Eq, Ord)

instance Show Stage where
  show s = case s of
    R -> "rt"
    C -> "ct"
    T -> "tt"
    StageMeta gl -> "?" ++ show (unGlobal gl)

data Term
  = Var Index Type
  | TypeType
  | FunIntro Term Type
  | FunType Term Term
  | FunElim Term Term
  -- Explicit `Stage` to make type inference unnecessary
  | StagedIntro Term Type Stage
  | StagedType Term Stage
  | StagedElim Term Type Term Stage
  | Let Term Term Term
  | Meta Global Type
  | InsertedMeta [BinderInfo] Global Type
  | ElabError
  | Value Value

shift :: Set Index -> Term -> Reader Int Term
shift bounds = \case
  Var ix ty ->
    if ix `member` bounds then
      pure $ Var ix ty
    else do
      amt <- ask
      pure $ Var (Index $ unIndex ix + amt) ty
  TypeType -> pure TypeType
  FunIntro body ty -> FunIntro <$> shift next body <*> shift bounds ty
  FunType inTy outTy -> FunType <$> shift bounds inTy <*> shift next outTy
  FunElim lam arg -> FunElim <$> shift bounds lam <*> shift bounds arg
  StagedIntro inner ty s -> StagedIntro <$> shift next inner <*> shift next ty <*> pure s
  StagedType innerTy s -> StagedType <$> shift next innerTy <*> pure s
  StagedElim scr scrTy body s -> StagedElim <$> shift bounds scr <*> shift bounds scrTy <*> shift next body <*> pure s
  Let def defTy body -> Let <$> shift bounds def <*> shift bounds defTy <*> shift next body
  Meta gl ty -> Meta <$> pure gl <*> shift bounds ty
  InsertedMeta bis gl ty -> InsertedMeta <$> pure bis <*> pure gl <*> shift bounds ty
  ElabError -> pure ElabError
  _ -> error "Unimplemented"
  where
    next :: Set Index
    next = insert (Index 0) $ Data.Set.map (\ix -> Index $ unIndex ix + 1) bounds

instance Show Term where
  show = showTerm False

showTerm :: Bool -> Term -> String
showTerm showTys term = case term of
  Var ix ty ->
    if showTys then
      "(i" ++ show (unIndex ix) ++ " : " ++ show ty ++ ")"
    else
      "i" ++ show (unIndex ix)
  TypeType -> "Type"
  FunIntro body ty ->
    if showTys then
      "{" ++ show body ++ "; : " ++ show ty ++ "}"
    else
      "{" ++ show body ++ "}"
  FunType inTy outTy -> show inTy ++ " -> " ++ show outTy
  FunElim lam arg -> "(" ++ show lam ++ " @ " ++ show arg ++ ")"
  StagedIntro inner innerTy stage -> "[" ++ show stage ++ "|" ++ show inner ++ "; : " ++ show innerTy ++ "]"
  StagedType innerTy stage -> "Quote " ++ show stage ++ "|" ++ show innerTy
  StagedElim scr ty body stage -> "splice " ++ show stage ++ "|" ++ show scr ++ " : " ++ show ty ++ " in " ++ show body
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
  Value v -> error "Bug?"