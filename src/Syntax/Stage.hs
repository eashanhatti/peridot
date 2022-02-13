module Syntax.Stage where

import Syntax.Variable

data Stage = Meta | Object | UniVar Global
  deriving (Eq)