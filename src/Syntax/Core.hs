module Syntax.Core where

import Syntax.Variable
import Syntax.Stage
import {-# SOURCE #-} Syntax.Telescope qualified as T

type Telescope = T.Telescope Term

data Declaration
  = Datatype Id Telescope
  | Constr Id Telescope Id [Term]
  | Term Term Term -- sig, def
  deriving (Eq)

data Term
  = FunType Term Term
  | FunIntro Term
  | FunElim Term Term
  | DatatypeType Id [Term]
  | DatatypeIntro Id [Term]
  | TypeType Stage
  | Var Index
  | Let [Declaration] Term
  | UniVar Global
  deriving (Eq)