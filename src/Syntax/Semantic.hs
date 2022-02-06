module Syntax.Semantic where

import Syntax.Telescope qualified as T

data Term
  = FunType Term Term

type Telescope = T.Telescope Term