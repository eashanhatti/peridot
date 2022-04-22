module Syntax.Core
( module Syntax.Core
, module Syntax.Common
) where

import Syntax.Common hiding(unId)
import Data.Sequence

type Signature = Term

data Declaration
  = MetaConst Id Signature
  | ObjConst Id Signature
  | Fresh Id Signature
  | Prove Id Signature
  | ObjTerm Id Signature Term -- sig, def
  | MetaTerm Id Signature Term -- sig, def
  | CFun Id (Seq Term) Term (CStatement Term)
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
  -- Object level
  = ObjFunType Term Term
  | ObjFunIntro Term
  | ObjFunElim Term Term
  | ObjConstIntro Id
  -- Low C level
  | CIntIntro Int
  | COp (COp Term)
  | CFunCall Term (Seq Term)
  -- Meta level
  | MetaFunType ApplyMethod Term Term
  | MetaFunIntro Term
  | MetaFunElim Term Term
  | MetaConstIntro Id
  | CodeCoreType Term
  | CodeCoreIntro Term
  | CodeCoreElim Term
  | CodeLowCTmType Term
  | CodeLowCTmIntro Term
  | CodeLowCTmElim Term
  | CodeLowCStmtType Term -- Carries return type
  | CodeLowCStmtIntro (CStatement Term)
  | CIntType
  | CVoidType
  | CPtrType Term
  | CValType ValueCategory Term
  | CFunType (Seq Term) Term
  -- Other
  | TypeType Stage
  | LocalVar Index
  | GlobalVar Id
  | Let (Seq Declaration) Term
  | UniVar Global
  | EElabError
  deriving (Eq, Show)

pattern CRValType ty = CValType RVal ty
pattern CLValType ty = CValType LVal ty

data Stage = Meta | Obj | Low Language | SUniVar Global
  deriving (Eq, Show)

data ValueCategory = LVal | RVal | VCUniVar Global
  deriving (Eq, Show)
