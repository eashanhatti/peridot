module Syntax.Telescope where

import Syntax.Semantic qualified as N
import Normalization
import Numeric.Natural

data Telescope a
  = Empty
  | Bind a (Telescope a)
  deriving (Foldable, Traversable, Functor)

deriving instance Eq a => Eq (Telescope a)

view :: Norm sig m => N.Term -> m (N.Telescope, N.Term)
view (N.FunType _ inTy outTy) = do
  vOutTy <- evalClosure outTy
  (tele, outTy') <- view vOutTy
  pure (Bind inTy tele, outTy')
view ty = pure (Empty, ty)

size :: Telescope a -> Natural
size Empty = 0
size (Bind _ tele) = 1 + size tele