module Syntax.Core where

import Syntax.Variable
import Syntax.Telescope qualified as T

type Telescope = T.Telescope Term

data Declaration
  = Datatype Id Telescope
  | Constr Id Telescope Id [Term]
  | Term Term Term

data Term
  = FunType Term Term
  | FunIntro Term
  | FunElim Term Term
  | ConstrIntro Id [Term]
  | Var Index
  | Let [Declaration] Term
  | ElabError