module Syntax.Object where

import Syntax.Extra

type Signature = Term

data Declaration
  = Term Id RuntimeRep Signature Term
  | ObjectConstant Id RuntimeRep Signature
  deriving (Show)

unId :: Declaration -> Id
unId (Term did _ _ _) = did
unId (ObjectConstant did _ _) = did

unSig :: Declaration -> Signature
unSig (Term _ _ sig _) = sig
unSig (ObjectConstant _ _ sig) = sig

type Type = Term

data Term
  = FunType Term Term
  | FunIntro RuntimeRep Term
  | FunElim Term Term RuntimeRep
  | IOType Term
  | IOIntroPure Term -- `pure`
  | IOIntroBind IOOperation Term -- `>>=`
  | UnitType
  | UnitIntro
  | ObjectConstantIntro Id
  | TypeType RuntimeRep
  | LocalVar Index
  | GlobalVar Id
  | Let [Declaration] Term
  deriving (Show)
