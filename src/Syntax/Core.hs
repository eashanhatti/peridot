module Syntax.Core where

import Syntax.Extra

type Signature = Term

data Declaration
  = MetaConstant Id Signature
  | ObjectConstant Id RuntimeRep Signature
  | Fresh Id Signature
  | Prove Id Signature
  | Term Id RuntimeRep Signature Term -- sig, def
  | DElabError
  deriving (Eq, Show)

unId :: Declaration -> Id
unId (ObjectConstant did _ _) = did
unId (MetaConstant did _) = did
unId (Term did _ _ _) = did
unId (Fresh did _) = did
unId (Prove did _) = did
unId DElabError = error "FIXME"

type Type = Term

data Term
  = MetaFunType ApplyMethod Term Term
  | MetaFunIntro Term
  | MetaFunElim Term Term
  | ObjectFunType RuntimeRep Term Term
  | ObjectFunIntro RuntimeRep Term
  | ObjectFunElim Term Term
  | MetaConstantIntro Id
  | ObjectConstantIntro Id
  | IOType Term
  | IOIntro1 Term -- `pure`
  | IOIntro2 IOOperation Term -- `>>=`
  | UnitType
  | UnitIntro
  | TypeType Stage
  | LocalVar Index
  | GlobalVar Id
  | Let [Declaration] Term
  | UniVar Global
  | EElabError
  deriving (Eq, Show)
