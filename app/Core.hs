module Core where

import Var

data BinderInfo = Abstract | Concrete
  deriving Show

-- type annotation
type Type = Term

data HoleName = HoleName Int
  deriving Show

data Stage = R | C | T | StageMeta Global
  deriving Eq

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
  | StagedElim Term Term Stage
  | Let Term Term Term
  | Meta Global Type
  | InsertedMeta [BinderInfo] Global Type
  | ElabError

instance Show Term where
  show = showTerm False

showTerm :: Bool -> Term -> String
showTerm showTys term = case term of
  Var ix ty ->
    if showTys then
      "(v" ++ show (unIndex ix) ++ " : " ++ show ty ++ ")"
    else
      "v" ++ show (unIndex ix)
  TypeType -> "Type"
  FunIntro body ty ->
    if showTys then
      "(\\" ++ show body ++ "; : " ++ show ty ++ ")"
    else
      "\\" ++ show body ++ ""
  FunType inTy outTy -> show inTy ++ " -> " ++ show outTy
  FunElim lam arg -> "(" ++ show lam ++ " " ++ show arg ++ ")"
  StagedIntro inner innerTy stage -> "[" ++ show stage ++ "|" ++ show inner ++ "; : " ++ show innerTy ++ "]"
  StagedType innerTy stage -> "Quote " ++ show stage ++ show innerTy
  StagedElim scr body stage -> "splice " ++ show stage ++ "|" ++ show scr ++ " in " ++ show body
  Let def defTy body -> "let " ++ show def ++ " : " ++ show defTy ++ " in\n" ++ show body
  Meta gl ty ->
    if showTys then
      "(?" ++ show (unGlobal gl) ++ " : " ++ show ty ++ ")"
    else
      "?" ++ show (unGlobal gl)
  InsertedMeta bis gl ty ->
    if showTys then
      "(?" ++ show (unGlobal gl) ++ " : " ++ show ty ++ ";" ++ (show $ map show bis) ++ ")"
    else
      "?" ++ show (unGlobal gl) ++ (show $ map show bis) ++ ""
  ElabError -> "<elab error>"