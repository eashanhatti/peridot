module Elaboration where

import Elaboration.Effect hiding(eval, zonk)
import Elaboration.Term qualified as EE
import Syntax.Surface qualified as S
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Normalization hiding(unTypeUVs)
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Carrier.Throw.Either
import Extra
import Syntax.Common
import Text.Megaparsec.Pos
import Data.Text(pack)
import Parser

elaborate = snd . elaborate'

elaborate' :: S.TermAst -> (QueryState, C.Term)
elaborate' term =
  let
    (qs, term') =
      run $
      runState (QueryState mempty mempty 1000 mempty mempty {-mempty-} mempty mempty) $
      evalState ElabState $
      runReader (NormContext (N.Env mempty mempty) mempty {-mempty-} mempty mempty) $
      runReader (ElabContext mempty (initialPos "<TODO>") mempty) $
      EE.check term (N.TypeType N.Obj)
    term'' =
      run $
      runReader (NormContext (N.Env mempty mempty) mempty (justs $ unTypeUVs qs) mempty)
      (eval term' >>= zonk)
  in
    (qs, term'')

elaborateFile :: String -> IO (Either String C.Term)
elaborateFile f = do
  r <- elaborateFile' f
  case r of
    Right r -> pure (Right (snd r))
    Left r -> pure (Left r)

elaborateFile' :: String -> IO (Either String (QueryState, C.Term))
elaborateFile' f = do
  s <- pack <$> readFile f
  pure (fmap elaborate' (parse s))
