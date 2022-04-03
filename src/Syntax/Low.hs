module Syntax.Low where

import Data.Sequence
import Syntax.Extra

data Program = Prog (Seq Declaration)

data Declaration = Function Id (Seq Binding) Term Representation

data Binding = Bound Id Representation

data Term
  = Do SimpleTerm Id Representation Term
  | Case Value (Seq Branch)
  | Simple SimpleTerm

data Branch = Branch Pattern Term

data SimpleTerm
  = App Id SimpleTerm
  | Pure Value
  | Alloc Value
  | Read Id
  | Write Id Value

data Value
  = VSum Word SimpleValue
  | VProd (Seq SimpleValue)

data SimpleValue
  = VWord Word
  | Var Id

data Pattern
  = PWord Word
  | PSum Word Binding
  | PProd (Seq Binding)

data Representation
  = RWord
  | Ptr Representation
  | RSum (Seq Representation)
  | RProd (Seq Representation)
