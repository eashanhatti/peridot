module Syntax.Low where

import Data.Sequence
import Syntax.Extra
import Numeric.Natural
import Data.Map

data Value
  = Var Id
  | Num Natural

data Instruction
  = StackAllocWord Value Value -- word, world
  | HeapAllocWord Value Value -- word, world
  | WritePtr Value Value -- ptr, world
  | ReadPtr Value -- ptr
  | PrintChar Char Value -- char, world

data Terminator
  = LocalJump Id (Seq Value)
  | NonlocalJump Value (Seq Value)

data Parameter = Param Id Type

data Binding = Bind
  { unNames :: Seq Id
  , unInst :: Instruction }

data BasicBlock = Block
  { unParams :: Seq Parameter
  , unBinds :: Seq Binding
  , unTerm :: Terminator }

data Program = Prog
  { unBBs :: Map Id BasicBlock }

data Type
  = Word
  | Ptr
  | BlockPtr (Seq Type)
  | World -- linear
