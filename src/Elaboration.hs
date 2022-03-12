module Elaboration where

import Elaboration.Effect
import Elaboration.Term qualified as EE
import Syntax.Surface qualified as S
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Normalization
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Carrier.Throw.Either
import Extra

elaborate = fst . elaborate'

elaborate' :: S.TermAst -> (ElabState, C.Term)
elaborate' term =
  run $
  runState (ElabState mempty 0 mempty mempty mempty) $
  runReader (NormContext (N.Env mempty mempty)) $
  evalState (NormState mempty) $
  evalState (QueryState mempty mempty) $
  runReader (ElabContext mempty) $
  EE.check term (N.IOType N.UnitType)
