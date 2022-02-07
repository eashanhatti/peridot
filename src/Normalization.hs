module Normalization where

import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Variable
import Control.Effect.Reader
import Control.Algebra(Has)
import Data.Functor.Identity

newtype Context = Context Level

type Eval sig m = Has (Reader Context) sig m

appClosure :: Eval sig m => N.Closure -> N.Term -> m N.Term
appClosure = undefined

evalClosure :: Eval sig m => N.Closure -> m N.Term
evalClosure = undefined

eval :: Eval sig m => C.Term -> m N.Term
eval = undefined

readback :: Eval sig m => N.Term -> m C.Term
readback = undefined

freeVar :: Eval sig m => m N.Term
freeVar = undefined