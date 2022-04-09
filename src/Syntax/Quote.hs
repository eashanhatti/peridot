module Syntax.Quote where

import Syntax.Extra

data TermQuote a
  = FunType a a
  | FunIntro a
  | FunElim a a
  | ConstantIntro Id
  | IOType a
  | IOIntroPure a -- `pure`
  | IOIntroBind IOOperation a -- `>>=`
  | UnitType
  | UnitIntro
  | TypeType
  | LocalVar Index
  | GlobalVar Id
  | Let [DeclarationQuote a] a
  | UniVar Global
  | ElabError
  deriving (Eq, Show)

data DeclarationQuote a
  = ObjectConstant Id a
  | Term Id a a
  deriving (Eq, Show)
