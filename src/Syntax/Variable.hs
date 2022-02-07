module Syntax.Variable where

import Numeric.Natural
import Data.Text
import Data.Hashable
import GHC.Generics

newtype Index = Index { unIndex :: Natural }
  deriving newtype (Num, Eq)

newtype Level = Level { unLevel :: Natural }
  deriving newtype (Num, Eq)

newtype Id = Id { unId :: Natural }
  deriving (Eq, Ord, Generic)

newtype Global = Global { unGlobal :: Natural }
  deriving newtype (Num, Eq)

instance Hashable Id

data Name = UserName Text | MachineName Natural
  deriving (Eq, Ord)