module Elaboration where

import Elaboration.Effect hiding(eval, zonk)
import Elaboration.Term qualified as EE
import Syntax.Surface qualified as S
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Normalization hiding(unTypeUVs)
import Normalization qualified as Norm
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Carrier.Throw.Either
import Data.Map qualified as Map
import Extra
import Syntax.Common
import Text.Megaparsec.Pos
import Data.Text(pack, Text)
import Parser
import Data.Maybe

elaborate = snd . elaborate'

infer' :: S.TermAst -> (QueryState, C.Term, C.Term)
infer' term =
  let
    (qs, (term', ty)) =
      run .
      runState (QueryState mempty mempty 1000 mempty mempty mempty mempty) .
      runReader (QueryContext Nothing) .
      evalState ElabState .
      runReader (NormContext (N.Env mempty mempty) mempty mempty mempty mempty) .
      runReader (ElabContext mempty (initialPos "<TODO>") mempty False) $
      EE.infer term
    ty' =
      run .
      runReader
        (NormContext
          (N.Env mempty mempty)
          mempty
          (fmap fromJust . Map.filter isJust $ unTypeUVs qs)
          mempty
          mempty) $
      Norm.zonk ty
  in (qs, term', ty')

readback :: N.Term -> C.Term
readback term =
  run .
  runReader (NormContext (N.Env mempty mempty) mempty mempty mempty mempty) $
  Norm.readback term

infer :: Text -> Either String (QueryState, C.Term, C.Term)
infer s = fmap infer' (parse prec0 s)

elaborate' :: S.TermAst -> (QueryState, C.Term)
elaborate' term =
  let
    (qs, term') =
      run .
      runState (QueryState mempty mempty 1000 mempty mempty mempty mempty) .
      runReader (QueryContext Nothing) .
      evalState ElabState .
      runReader (NormContext (N.Env mempty mempty) mempty mempty mempty mempty) .
      runReader (ElabContext mempty (initialPos "<TODO>") mempty False) $
      EE.check term N.ObjTypeType
    term'' =
      run $
      runReader
        (NormContext
          (N.Env mempty mempty)
          mempty
          (justs $ unTypeUVs qs)
          mempty
          mempty)
      (eval term' >>= zonk)
  in
    (qs, term')

elaborateFile :: String -> IO (Either String C.Term)
elaborateFile f = do
  r <- elaborateFile' f
  case r of
    Right r -> pure (Right (fst r))
    Left r -> pure (Left r)

swap (x, y) = (y, x)

elaborateFile' :: String -> IO (Either String (C.Term, QueryState))
elaborateFile' f = do
  s <- pack <$> readFile f
  pure (fmap (swap . elaborate') (parse toplevel s))