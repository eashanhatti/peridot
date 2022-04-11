module Syntax.Core where

import Syntax.Extra
import Syntax.Quote qualified as Q

type TermQuote = Q.TermQuote Term

type Signature = Term

data Declaration
  = MetaConstant Id Signature
  | ObjectConstant Id Signature
  | Fresh Id Signature
  | Prove Id Signature
  | Term Id Signature Term -- sig, def
  | DElabError
  deriving (Eq, Show)

unId :: Declaration -> Id
unId (ObjectConstant did _) = did
unId (MetaConstant did _) = did
unId (Term did _ _) = did
unId (Fresh did _) = did
unId (Prove did _) = did
unId DElabError = error "FIXME"

type Type = Term

data Term
  = MetaFunType ApplyMethod Term Term
  | MetaFunIntro Term
  | MetaFunElim Term Term
  | ObjectFunType Term Term
  | ObjectFunIntro Term
  | ObjectFunElim Term Term
  | MetaConstantIntro Id
  | ObjectConstantIntro Id
  | IOType Term
  | IOIntroPure Term -- `pure`
  | IOIntroBind IOOperation Term -- `>>=`
  | UnitType
  | UnitIntro
  | QuoteIntro TermQuote
  | QuoteType Term
  | WorldType
  | WordType
  | PtrType
  | BasicBlockType [Term]
  | InstType
  | TypeType Stage
  | UnqTypeType
  | LocalVar Index
  | GlobalVar Id
  | Let [Declaration] Term
  | UniVar Global
  | EElabError
  deriving (Eq, Show)
