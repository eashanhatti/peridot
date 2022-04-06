module Syntax.Quote where

import Syntax.Extra

data TermQuote a
  = ObjectFunType a a
  | ObjectFunIntro a
  | ObjectFunElim a a
  | ObjectConstantIntro Id
  | IOType a
  | IOIntroPure a -- `pure`
  | IOIntroBind IOOperation a -- `>>=`
  | UnitType
  | UnitIntro
  | TypeType
  | LocalVar Index
  | GlobalVar Id
  | Let [DeclarationQuote a] a
  deriving (Eq, Show)

data DeclarationQuote a
  = ObjectConstant Id a
  | Term Id a a
  deriving (Eq, Show)
