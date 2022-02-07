module Elaboration.Telescope where

import Syntax.Semantic qualified as N
import Syntax.Telescope qualified as T
import Syntax.Core qualified as C
import Elaboration.Query
import Syntax.Surface
import Normalization

view :: Eval sig m => N.Term -> m (N.Telescope, N.Term)
view (N.FunType inTy outTy) = do
  vOutTy <- evalClosure outTy
  (tele, outTy') <- view vOutTy
  pure (T.Bind inTy tele, outTy')
view ty = pure (T.Empty, ty)

check :: Eval sig m => TelescopeAst -> N.Term -> m (C.Telescope, [NameAst])
check (TeleAst tele) goal = undefined