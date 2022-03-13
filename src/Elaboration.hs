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
import Text.Megaparsec.Pos
import Data.Text(pack)
import Parser

elaborate = snd . elaborate'

elaborate' :: S.TermAst -> (QueryState, C.Term)
elaborate' term =
  run $
  runState (QueryState mempty mempty 0 mempty mempty mempty mempty) $
  evalState ElabState $
  runReader (NormContext (N.Env mempty mempty)) $
  evalState (NormState mempty) $
  runReader (ElabContext mempty (initialPos "<TODO>")) $
  EE.check term (N.IOType N.UnitType)

elaborateFile :: String -> IO (Either String C.Term)
elaborateFile f = do
  s <- pack <$> readFile f
  pure (fmap elaborate (parse s))
