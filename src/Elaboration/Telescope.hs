module Elaboration.Telescope where

import Syntax.Semantic qualified as N
import Syntax.Telescope qualified as T
import Syntax.Core qualified as C
import Syntax.Surface

view :: N.Term -> (N.Telescope, N.Term)
view (N.FunType inTy outTy) =
  let (tele, outTy') = view outTy
  in (T.Bind inTy tele, outTy')
view ty = (T.Empty, ty)

check :: TelescopeAst -> N.Term -> Query (C.Telescope, [NameAst])
check (TeleAst tele) goal = go tele where
  go T.Empty = pure (T.Empty, [])
  go (T.Bind ty tele) = do
    cTy <- check ty goal