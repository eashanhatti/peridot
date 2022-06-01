module Syntax.Core
( module Syntax.Core
, module Syntax.Common
) where

import Syntax.Common hiding(unId, Declaration)
import Syntax.Common qualified as Cm
import Data.Map
import Data.Sequence
import Numeric.Natural

unId :: Declaration -> Id
unId (MetaConst did _) = did
unId (MetaTerm did _ _) = did
unId (ObjTerm did _ _) = did
unId (CTerm did _ _) = did
unId DElabError = error "FIXME"

type Type = Term

type Declaration = Cm.Declaration Term

data Term
  -- Object level
  = ObjFunType PassMethod Term Term
  | ObjFunIntro Term
  | ObjFunElim Term Term
  | TwoElim Term Term Term
  | RecType (Seq (Field, Term))
  | RecIntro (Seq (Field, Term))
  | RecElim Term Field
  | SingElim Term
  -- Meta level
  | MetaFunType PassMethod Term Term
  | MetaFunIntro Term
  | MetaFunElim Term Term
  | CodeCoreElim Term
  -- Other
  | LocalVar Index
  | GlobalVar Id
  | Let (Seq Declaration) Term
  | UniVar Global
  | Rigid (RigidTerm Term)
  deriving (Eq, Show)

pattern ObjTypeType = Rigid (TypeType Obj)
pattern MetaTypeType = Rigid (TypeType Meta)
pattern LowCTypeType = Rigid (TypeType LowC)
pattern ListTypeType = Rigid (TypeType List)
