module Syntax.Core
( module Syntax.Core
, module Syntax.Common
) where

import Syntax.Common hiding(unId)
import Data.Sequence

type Signature = Term

data Declaration
  = MetaConst Id Signature
  | PropConst Id Signature
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
unId (PropConst did _) = did
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
  -- Meta level
  | MetaFunType Term Term
  | MetaFunIntro Term
  | MetaFunElim Term Term
  | CodeCoreElim Term
  | CodeLowCTmElim Term
  -- Other
  | TypeType Universe
  | LocalVar Index
  | GlobalVar Id
  | Let (Seq Declaration) Term
  | UniVar Global
  | Rigid (RigidTerm Term)
  deriving (Eq, Show)

data Universe = Meta | Obj | Low Language | Prop | SUniVar Global
  deriving (Eq, Show)
