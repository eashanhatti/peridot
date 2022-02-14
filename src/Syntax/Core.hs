module Syntax.Core where

import Syntax.Variable
import Syntax.Stage
import {-# SOURCE #-} Syntax.Telescope qualified as T

type Telescope = T.Telescope Term

data Declaration
  = Datatype Id Telescope Stage
  | Constr Id Telescope Id [Term]
  | Term Id Term Term -- sig, def
  | DElabError
  deriving (Eq)

unId :: Declaration -> Id
unId (Datatype did _ _) = did
unId (Constr did _ _ _) = did
unId (Term did _ _) = did
unId DElabError = undefined -- FIXME

data Term
  = FunType Term Term
  | FunIntro Term
  | FunElim Term Term
  | DatatypeType Id [Term]
  | DatatypeIntro Id [Term]
  | TypeType Stage
  | LocalVar Index
  | GlobalVar Id
  | Let [Declaration] Term
  | UniVar Global
  | EElabError
  deriving (Eq)