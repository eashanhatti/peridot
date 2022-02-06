module Elaboration.Telescope where

import Syntax.Semantic
import Syntax.Telescope qualified as T

view :: Term -> (Telescope, Term)
view (FunType inTy outTy) =
  let (tele, outTy') = view outTy
  in (T.Bind inTy tele, outTy')
view ty = (T.Empty, ty)