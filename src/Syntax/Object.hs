module Syntax.Object where

import Syntax.Extra

type Signature = Term

data Declaration
  = Term Id Signature Term
  | ObjectConstant Id Signature
  deriving (Show)

unId :: Declaration -> Id
unId (Term did _ _) = did
unId (ObjectConstant did _) = did

unSig :: Declaration -> Signature
unSig (Term _ sig _) = sig
unSig (ObjectConstant _ sig) = sig

type Type = Term

data Term
  = FunType Term Term
  | FunIntro Term
  | FunElim Term Term
  | IOType Term
  | IOIntroPure Term -- `pure`
  | IOIntroBind IOOperation Term -- `>>=`
  | UnitType
  | UnitIntro
  | ObjectConstantIntro Id
  | TypeType
  | LocalVar Index
  | GlobalVar Id
  | Let [Declaration] Term
  deriving (Show)
