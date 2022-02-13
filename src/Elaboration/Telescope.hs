module Elaboration.Telescope where

import Syntax.Semantic qualified as N
import Syntax.Telescope qualified as T
import Syntax.Core qualified as C
import Elaboration.Effect
import Syntax.Surface
import Normalization

check :: Elab sig m => TelescopeAst -> N.Term -> m (C.Telescope, [NameAst])
check (TeleAst tele) goal = undefined