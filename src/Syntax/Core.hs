module Syntax.Core
( module Syntax.Core
, module Syntax.Common
) where

import Syntax.Common hiding(unId, Declaration)
import Syntax.Common qualified as Cm
import Data.Map
import Data.Sequence
import Numeric.Natural

type Type = Term

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
  | CodeObjElim Term
  | CodeCElim Term
  -- Other
  | LocalVar Index
  | GlobalVar Id
  | UniVar Global
  | Rigid (RigidTerm Term)
  | Declare Universe Term Term Term -- ty, name, cont
  | Define Universe Term Term Term -- name, def, cont
  deriving (Eq, Show)

pattern ObjTypeType = Rigid (TypeType Obj)
pattern MetaTypeType = Rigid (TypeType Meta)
pattern LowCTypeType = Rigid (TypeType LowC)
pattern ListTypeType = Rigid (TypeType List)
