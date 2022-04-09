module Syntax.Low where

import Data.Sequence
import Syntax.Extra
import Numeric.Natural

data Value
  = Var Id
  | Num Natural

data Instruction
  = StackAllocWord Value Value -- word, mem
  | HeapAllocWord Value Value -- word, mem
  | WritePtr Value Value -- ptr, mem
  | ReadPtr Value -- ptr

data Terminator = Jump Id (Seq Value)

data Parameter = Param Id Type

data Binding = Bind
  { unBinds :: Seq (Id, Type)
  , unInst :: Instruction }

data BasicBlock = Block
  { unParams :: Seq Parameter
  , unInsts :: Seq Binding
  , unTerm :: Terminator }

data Program = Prog
  { unBBs :: Seq BasicBlock }

data Type
  = Word
  | Ptr
  | Memory -- linear
