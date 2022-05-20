module Syntax.Common where

import Numeric.Natural
import Data.Text
import Data.Hashable
import GHC.Generics
import Data.Map qualified as Map
import Data.Sequence

data Language = C
  deriving (Eq, Show)

newtype Index = Index { unIndex :: Natural }
  deriving (Num, Eq, Ord, Enum, Real, Integral, Show)

newtype Level = Level { unLevel :: Natural }
  deriving (Num, Eq, Enum, Show)

newtype Id = Id { unId :: Natural }
  deriving (Eq, Ord, Generic, Num, Enum, Real, Integral, Show)

data Global
  = UVGlobal Natural
  | LVGlobal Natural
  deriving (Eq, Ord, Show)

unGlobal (UVGlobal n) = n
unGlobal (LVGlobal n) = n

instance Hashable Id

data Name = UserName Text | MachineName Natural
  deriving (Eq, Ord, Show)

data CStatement a
  = VarDecl a
  | Assign a a
  | If a (CStatement a) (CStatement a)
  | Block (CStatement a) (CStatement a)
  | Return (Maybe a)
  | CodeLowCStmtElim a
  deriving (Eq, Show, Functor, Foldable, Traversable)

data COp a
  = Ref a
  | Deref a
  | Add a a
  | Sub a a
  | Less a a
  | Grtr a a
  | Eql a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

data RigidTerm a
  -- Object level
  = ObjConstIntro Id
  | TwoType
  | TwoIntro0
  | TwoIntro1
  | SigmaType a a
  | SigmaIntro a a
  | SingType a
  | SingIntro a
  | ObjIdType a a
  | ObjIdIntro a
  -- Low C level
  | CIntIntro Int
  | COp (COp a)
  | CFunCall a (Seq a)
  -- Meta level
  | MetaConstIntro Id
  | CodeCoreType a
  | CodeCoreIntro a
  | CodeLowCTmType a
  | CodeLowCTmIntro a
  | CodeLowCStmtType a -- Carries return type
  | CodeLowCStmtIntro (CStatement a)
  | CPtrType a
  | CIntType
  | CVoidType
  | CFunType (Seq a) a
  -- Propositions
  | PropConstIntro Id
  | ImplType a a
  | ConjType a a
  | DisjType a a
  | AllType a
  | SomeType a
  | PropIdType a a
  -- Other
  | ElabError
  deriving (Eq, Show, Functor, Foldable, Traversable)

data Declaration a
  = MetaConst Id a
  | ObjTerm Id a a -- sig, def
  | MetaTerm Id a a -- sig, def
  | CFun Id (Seq a) a (CStatement a)
  | DElabError
  deriving (Eq, Show, Functor, Foldable, Traversable)
