module Syntax.Quote where

import Syntax.Extra
import Data.Sequence

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
  | UnqTypeType
  -- | LocalVar Index
  -- | GlobalVar Id
  | Let (Seq (DeclarationQuote a)) a
  | UniVar Global
  | ElabError
  | InstType
  | InstIntroStackAllocWord a a a -- word, world, cont
  | InstIntroHeapAllocWord a a a -- word, world, cont
  | InstIntroWritePtr a a a -- ptr, world, cont
  | InstIntroReadPtr a a -- ptr, cont
  | InstIntroPrintChar Char a a a -- char, world, cont
  | InstIntroJump a (Seq a)
  | BasicBlockType (Seq a)
  | BasicBlockIntro a
  | WorldType
  | WordType
  | PtrType
  | BlockPtrType
  deriving (Eq, Show, Functor, Foldable, Traversable)

data DeclarationQuote a
  = ObjectConstant Id a
  | Term Id a a
  deriving (Eq, Show, Functor, Foldable, Traversable)
