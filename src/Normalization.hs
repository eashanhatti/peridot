module Normalization where

import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Control.Monad.Reader.Class
import Data.Functor.Identity

newtype EvalT m a = EvalT (ReaderT m Level)
	deriving newtype (MonadReader)
type Eval = EvalT Identity

appClosure :: N.Closure -> N.Term -> Eval N.Term
appClosure = undefined

eval :: C.Term -> Eval N.Term
eval = undefined

readback :: N.Term -> Eval C.Term
readback = undefined