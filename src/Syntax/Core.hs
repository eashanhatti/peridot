module Syntax.Core where

import Syntax.Extra

type Signature = Term

data Declaration
  = Datatype Id Signature
  | Constr Id Signature
  | Axiom Id Signature
  | Fresh Id Signature
  | Term Id Signature Term -- sig, def
  | DElabError
  deriving (Eq)

unId :: Declaration -> Id
unId (Datatype did _) = did
unId (Constr did _) = did
unId (Term did _ _) = did
unId DElabError = undefined -- FIXME

data Term
  = FunType ApplyMethod Term Term
  | FunIntro Term
  | FunElim Term Term
  | DatatypeType Id
  | DatatypeIntro Id
  | PropType Id [Term]
  | ConjType Term Term
  | TypeType Stage
  | LocalVar Index
  | GlobalVar Id
  | Let [Declaration] Term
  | UniVar Global
  | EElabError
  deriving (Eq)