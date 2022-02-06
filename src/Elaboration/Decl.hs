module Elaboration.Decl where

import Syntax.Surface
import Syntax.Core qualified as C
import {-# SOURCE #-} Elaboration.Query

check :: DeclarationAst -> Query C.Declaration
check = undefined