module Syntax.Core where

import Syntax.Extra

type Signature = Term

data Declaration
  = MetaConstant Id Signature
  | ObjectConstant Id Signature
  | Fresh Id Signature
  | Term Id Signature Term -- sig, def
  | DElabError
  deriving (Eq)

unId :: Declaration -> Id
unId (ObjectConstant did _) = did
unId (MetaConstant did _) = did
unId (Term did _ _) = did
unId (Fresh did _) = did
unId DElabError = error "FIXME"

data Term
  = FunType ApplyMethod Term Term
  | FunIntro Term
  | FunElim Term Term
  | MetaConstantIntro Id
  | ObjectConstantIntro Id
  | PropType Id [Term]
  | ConjType Term Term
  | TypeType Stage
  | LocalVar Index
  | GlobalVar Id
  | Let [Declaration] Term
  | UniVar Global
  | EElabError
  deriving (Eq)