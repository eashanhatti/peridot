module Syntax.Core where

import Syntax.Variable

data Telescope
  = Empty
  | Bind Term Telescope

data Declaration
  = Datatype Global Telescope
  | Constr Global Telescope Global [Term]
  | Definition Term Term

data Term
  = FunType Term Term
  | FunIntro Term
  | FunElim Term Term
  | ConstrIntro Global [Term]
  | Var Index
  | Let [Declaration] Term