module Syntax.Core where

import Syntax.Extra

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

data Stage = Meta | Object Term | SUniVar Global
  deriving (Eq, Show)

data Term
  = FunType ApplyMethod Term Term
  | FunIntro Type Term
  | FunElim Term Term
  | MetaConstantIntro Id
  | ObjectConstantIntro Id
  | IOType Term
  | IOIntroPure Term -- `pure`
  | IOIntroBind IOOperation Term -- `>>=`
  | UnitType
  | UnitIntro
  | TypeType Stage
  | RepType
  | RepIntroPtr
  | RepIntroLazy
  | RepIntroWord
  | RepIntroProd [Term]
  | RepIntroSum [Term]
  | RepIntroErased
  | LocalVar Index
  | GlobalVar Id
  | Let [Declaration] Term
  | UniVar Global
  | EElabError
  deriving (Eq, Show)
