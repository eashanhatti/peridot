module Syntax.Extra where

import Numeric.Natural
import Data.Text
import Data.Hashable
import GHC.Generics

data ApplyMethod = Explicit | Implicit
  deriving (Eq)

data Stage = Meta | Object RuntimeRep | SUniVar Global
  deriving (Eq)

newtype Index = Index { unIndex :: Natural }
  deriving (Num, Eq, Ord, Enum, Real, Integral)

newtype Level = Level { unLevel :: Natural }
  deriving (Num, Eq, Enum)

newtype Id = Id { unId :: Natural }
  deriving (Eq, Ord, Generic, Num, Enum, Real, Integral)

newtype Global = Global { unGlobal :: Natural }
  deriving (Num, Eq, Ord)

instance Hashable Id

data Name = UserName Text | MachineName Natural
  deriving (Eq, Ord)

data IOOperation = PutChar Char
  deriving (Eq)

data RuntimeRep
  = Ptr
  | Lazy
  | Word
  | Prod [RuntimeRep]
  | Sum [RuntimeRep]
  | Erased
  | RUniVar Global
  deriving (Eq)
