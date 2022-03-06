module Syntax.Object where

import Syntax.Extra

type Signature = Term

data Declaration
  = Term Id Signature Term
  | ObjectConstant Id Signature

unSig :: Declaration -> Signature
unSig (Term _ sig _) = sig
unSig (ObjectConstant _ sig) = sig

type Type = Term

data Term
  = FunType Term Term
  | FunIntro Type Term
  | FunElim Term Term
  | IOType Term
  | IOIntro1 Term -- `pure`
  | IOIntro2 IOOperation Term -- `>>=`
  | UnitType
  | UnitIntro
  | TypeType Stage
  | LocalVar Index
  | GlobalVar Id
  | Let [Declaration] Term
