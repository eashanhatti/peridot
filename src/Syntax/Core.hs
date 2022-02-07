module Syntax.Core where

import Syntax.Variable
import Syntax.Stage
import Syntax.Telescope qualified as T

type Telescope = T.Telescope Term

data Declaration
  = Datatype Id Telescope
  | Constr Id Telescope Id [Term]
  | Term Term Term
  deriving (Eq)

data Term
  = FunType Term Term
  | FunIntro Term
  | FunElim Term Term
  | DatatypeIntro Id [Term]
  | TypeType Stage
  | Var Index
  | Let [Declaration] Term
  deriving (Eq)