module Syntax.Extra where

import Numeric.Natural
import Data.Text
import Data.Hashable
import GHC.Generics
import Data.Map qualified as Map

data ApplyMethod = Explicit | Implicit
  deriving (Eq, Show)

data Stage = Meta | Object | SUniVar Global
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

data IOOperation = PutChar Char
  deriving (Eq, Show)
