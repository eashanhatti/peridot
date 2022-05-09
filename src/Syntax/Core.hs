module Syntax.Core
( module Syntax.Core
, module Syntax.Common
) where

import Syntax.Common hiding(unId, Declaration)
import Syntax.Common qualified as Cm
import Data.Sequence

unId :: Declaration -> Id
unId (ObjConst did _) = did
unId (MetaConst did _) = did
unId (PropConst did _) = did
unId (MetaTerm did _ _) = did
unId DElabError = error "FIXME"

type Type = Term

type Declaration = Cm.Declaration Term

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
