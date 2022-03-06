module Syntax.STG where

import Syntax.Extra
import Data.Set qualified as Set

data Declaration
  = Fun Id (Set.Set Id) [Binding] Term
  | Thunk Id Term

data Value
  = Var Id
  | Con Id [Value]
  | Arrow Value Value
  | Unit
  | UnitType
  | IOType Value
  | Univ RuntimeRep

-- data Branch = Branch [Binding] Term

data Binding = Binding RuntimeRep Id

data Term
  = App Value [Value]
  -- | Case Value [Branch]
  | Letrec [Declaration] Term
  | Let [(Binding, Term)] Term
  | DoIO IOOperation Term
  | Val Value
