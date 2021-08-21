module Core where

import Var

data BinderInfo = Abstract | Concrete
  deriving Show

-- type annotation
type Type = Term

data HoleName = HoleName Int
  deriving Show

data Term
  = Var Index Type
  | TypeType
  | FunIntro Term Type
  | FunType Term Term
  | FunElim Term Term
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