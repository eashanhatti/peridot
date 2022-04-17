module Syntax.Core where

import Syntax.Extra
import Data.Sequence

type Signature = Term

data Declaration
  = MetaConst Id Signature
  | ObjConst Id Signature
  | Fresh Id Signature
  | Prove Id Signature
  | Term Id Signature Term -- sig, def
  | DElabError
  deriving (Eq, Show)

unId :: Declaration -> Id
unId (ObjConst did _) = did
unId (MetaConst did _) = did
unId (Term did _ _) = did
unId (Fresh did _) = did
unId (Prove did _) = did
unId DElabError = error "FIXME"

type Type = Term

data Term
  = MetaFunType ApplyMethod Term Term
  | MetaFunIntro Term
  | MetaFunElim Term Term
  | ObjFunType Term Term
  | ObjFunIntro Term
  | ObjFunElim Term Term
  | MetaConstIntro Id
  | ObjConstIntro Id
  | IOType Term
  | IOIntroPure Term -- `pure`
  | IOIntroBind IOOperation Term -- `>>=`
  | CodeCoreType Term
  | CodeCoreIntro Term
  | CodeCoreElim Term
  | CodeLowType Term
  | CodeLowIntro Term
  | CodeLowElim Term
  | UnitType
  | UnitIntro
  | TypeType Stage
  | LocalVar Index
  | GlobalVar Id
  | Let (Seq Declaration) Term
  | UniVar Global
  | EElabError
  deriving (Eq, Show)
