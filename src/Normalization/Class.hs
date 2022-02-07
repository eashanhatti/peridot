module Normalization.Class where

import Syntax.Semantic
import Normalization qualified as E
import Control.Monad.Logic

class Monad m => MonadEval m where
  appClosure :: N.Closure -> N.Term -> m N.Term
  eval :: C.Term -> m N.Term
  readback :: N.Term -> m C.Term

instance MonadEval m => MonadEval (LogicT m a) where
  appClosure = undefined
  eval = undefined
  readback = undefined