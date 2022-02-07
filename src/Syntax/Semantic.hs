module Syntax.Semantic where

import Syntax.Variable
import Syntax.Stage
import Syntax.Telescope qualified as T

data Declaration
  = Datatype Id Telescope
  | Constr Id Telescope Id [Term]
  | Term Term Term

data Term
  = FunType Term Term
  | FunIntro Term
  | DatatypeIntro Id [Term]
  | TypeType Stage
  | Var Index
  | Let [Declaration] Term
  | UniVar Global

type Telescope = T.Telescope Term