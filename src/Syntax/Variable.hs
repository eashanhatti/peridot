module Syntax.Variable where

import Numeric.Natural

newtype Index = Index { unIndex :: Natural }

newtype Global = Global { unGlobal :: Natural }