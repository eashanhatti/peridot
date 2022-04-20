module Syntax.Core where

import Syntax.Common
import Data.Sequence

type Signature = Term

data Declaration
  = MetaConst Id Signature
  | ObjConst Id Signature
  | Fresh Id Signature
  | Prove Id Signature
  | ObjTerm Id Signature Term -- sig, def
  | MetaTerm Id Signature Term -- sig, def
  | CFun Id (Seq CType) CType (CStatement Term)
  | DElabError
  deriving (Eq, Show)

unId :: Declaration -> Id
unId (ObjConst did _) = did
unId (MetaConst did _) = did
unId (ObjTerm did _ _) = did
unId (MetaTerm did _ _) = did
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
  | CodeCoreType Term
  | CodeCoreIntro Term
  | CodeCoreElim Term
  | CodeLowCTmType Term
  | CodeLowCTmIntro Term
  | CodeLowCTmElim Term
  | TypeType Stage
  | LocalVar Index
  | GlobalVar Id
  | Let (Seq Declaration) Term
  | UniVar Global
  | EElabError
  deriving (Eq, Show)
