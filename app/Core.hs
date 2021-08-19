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
