module Syntax.Object where

import Syntax.Extra
import Data.Sequence

type Signature = Term

data Declaration
  = Term Id Signature Term
  | ObjConst Id Signature
  deriving (Show)

unId :: Declaration -> Id
unId (Term did _ _) = did
unId (ObjConst did _) = did

unSig :: Declaration -> Signature
unSig (Term _ sig _) = sig
unSig (ObjConst _ sig) = sig

type Type = Term

data Term
  = FunType Term Term
  | FunIntro Term
  | FunElim Term Term
  | IOType Term
  | IOIntroPure Term -- `pure`
  | IOIntroBind IOOperation Term -- `>>=`
  | UnitType
  | UnitIntro
  | ObjConstIntro Id
  | TypeType
  | LocalVar Index
  | GlobalVar Id
  | Let (Seq Declaration) Term
  deriving (Show)
