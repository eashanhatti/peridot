module Syntax.STG where

import Syntax.Extra

data Declaration
  = Fun [Id] [(RuntimeRep, Id)] RuntimeRep ComplexTerm
  | Thunk ComplexTerm

data ComplexTerm
  = Let [(Id, Declaration)] [(Id, SimpleTerm)] SimpleTerm
  | Val SimpleTerm

data SimpleTerm
  = Var Id
  | App SimpleTerm [SimpleTerm]
