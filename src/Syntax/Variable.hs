module Syntax.Variable where

import Numeric.Natural
import Data.Text
import Data.Hashable
import GHC.Generics

newtype Index = Index { unIndex :: Natural }
  deriving (Num, Eq, Ord, Enum, Real, Integral)

newtype Level = Level { unLevel :: Natural }
  deriving (Num, Eq, Enum)

newtype Id = Id { unId :: Natural }
  deriving (Eq, Ord, Generic, Num)

newtype Global = Global { unGlobal :: Natural }
  deriving (Num, Eq, Ord)

instance Hashable Id

data Name = UserName Text | MachineName Natural
  deriving (Eq, Ord)