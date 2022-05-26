module Syntax.Core
( module Syntax.Core
, module Syntax.Common
) where

import Syntax.Common hiding(unId, Declaration)
import Syntax.Common qualified as Cm
import Data.Map
import Data.Sequence

unId :: Declaration -> Id
unId (MetaConst did _) = did
unId (MetaTerm did _ _) = did
unId (ObjTerm did _ _) = did
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

data Universe = Meta | Obj | Low Language | SUniVar Global
  deriving (Eq, Show)
