module PartialEval where

import Norm(eval, readback)
import Core(Term, Stage(..))
import Control.Monad.Reader(runReader)
import Data.Set(fromList)
import Var

partialEval :: Term -> Term
partialEval term =
  let value = runReader (eval term) (Level 0, mempty, fromList [T, C], mempty)
  in runReader (readback value) (Level 0, mempty, fromList [T, C], mempty)