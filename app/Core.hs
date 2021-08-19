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
  deriving Show

-- data TermPath
--   = Top
--   | FunIntroBody TermPath Type
--   | FunIntroType Term TermPath
--   | FunTypeIn TermPath Term
--   | FunTypeOut Term TermPath 
--   | FunElimLam TermPath Term
--   | FunElimArg Term TermPath
--   | LetDef TermPath Term
--   | LetBody Term TermPath