module Syntax.STG where

import Syntax.Extra
import Data.Set qualified as Set

data Declaration
  = Fun Id (Set.Set Id) [Binding] Term
  deriving (Show)

unName :: Declaration -> Id
unName (Fun name _ _ _) = name

data Value
  = Var Id
  | Con Id [Value]
  | Arrow Value Value
  | Unit
  | UnitType
  | IOType Value
  | Univ RuntimeRep
  deriving (Show)

-- data Branch = Branch [Binding] Term

data Binding = Binding RuntimeRep Id
  deriving (Show)

data Term
  = App Value [Value]
  -- | Case Value [Branch]
  | Letrec [Declaration] Term
  | Let [(Binding, Term)] Term
  | DoIO IOOperation Term
  | Val Value
  deriving (Show)
