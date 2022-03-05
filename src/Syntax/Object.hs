module Syntax.Object where

import Syntax.Extra

type Signature = Term

data Declaration
  = Term Id Signature Term

data Term
  = FunType Term Term
  | FunIntro Term
  | FunElim Term Term
  | IOType Term
  | IOIntro1 Term -- `pure`
  | IOIntro2 Term Term -- `>>=`
  | IOIntro3 IOOperation
  | UnitType
  | UnitIntro
  | TypeType Stage
  | LocalVar Index
  | GlobalVar Id
  | Let [Declaration] Term
