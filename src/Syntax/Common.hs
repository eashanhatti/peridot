module Syntax.Common where

import Numeric.Natural
import Data.Text
import Data.Hashable
import GHC.Generics
import Data.Map qualified as Map
import Data.Sequence

data ApplyMethod = Explicit | Implicit
  deriving (Eq, Show)

data Language = C
  deriving (Eq, Show)

data Stage = Meta | Obj | Low Language | SUniVar Global
  deriving (Eq, Show)

newtype Index = Index { unIndex :: Natural }
  deriving (Num, Eq, Ord, Enum, Real, Integral, Show)

newtype Level = Level { unLevel :: Natural }
  deriving (Num, Eq, Enum, Show)

newtype Id = Id { unId :: Natural }
  deriving (Eq, Ord, Generic, Num, Enum, Real, Integral, Show)

newtype Global = Global { unGlobal :: Natural }
  deriving (Num, Eq, Ord, Show)

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
  deriving (Eq, Show)

data COp a
  = Ref a
  | Deref a
  | Add a a
  | Sub a a
  | Less a a
  | Grtr a a
  | Eql a a
  deriving (Eq, Show)
