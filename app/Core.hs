module Core where

import Var

data BinderInfo = Abstract | Concrete
  deriving Show

-- type annotation
type Type = Term

data Term
  = Var Index Type
  | TypeType
  | FunIntro Term Type
  | FunType Term Term
  | FunElim Term Term
  | Let Term Term
  | Meta Global Type
  | InsertedMeta [BinderInfo] Global Type
  deriving Show