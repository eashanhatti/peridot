module Elaboration where

import Elaboration.Effect hiding(eval, zonk)
import Elaboration.Term qualified as EE
import Elaboration.Declaration qualified as ED
import Syntax.Surface qualified as S
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Normalization hiding(unTypeUVs, eval)
import Normalization qualified as Norm
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Carrier.Throw.Either
import Data.Map qualified as Map
import Data.Set qualified as Set
import Extras
import Syntax.Common
import Text.Megaparsec.Pos
import Data.Text(pack, Text)
import Parser
import Data.Maybe
import Control.Monad
import Control.Monad.IO.Class

infer' :: S.TermAst -> IO(QueryState, C.Term, C.Term)
infer' term = do
  (qs, (term', ty)) <-
    liftIO .
    runState (QueryState mempty mempty 1000 mempty mempty mempty mempty mempty mempty mempty 2000 mempty) .
    runReader (QueryContext Nothing) .
    evalState ElabState .
    runReader (NormContext (N.Env mempty mempty) mempty mempty mempty mempty) .
    runReader (ElabContext mempty (initialPos "<TODO>") mempty False) $
    EE.infer term
  let
    ty' =
      run .
      runReader
        (NormContext
          (N.Env mempty mempty)
          mempty
          (justs . unTypeUVs $ qs)
          (Elaboration.Effect.unUVEqs qs)
          mempty) $
      Norm.zonk ty
    term'' =
      run .
      runReader
        (NormContext
          (N.Env mempty mempty)
          mempty
          (justs . unTypeUVs $ qs)
          mempty
          mempty) $
      (Norm.eval >=> Norm.normalize) term'
  pure (qs, term'', ty')

normalize :: N.Term -> Map.Map Global UVSolution -> Map.Map Global (Set.Set Global) -> C.Term
normalize term sols eqs =
  run .
  runReader (NormContext (N.Env mempty mempty) mempty sols eqs mempty) $
  Norm.normalize term

zonk :: N.Term -> Map.Map Global UVSolution -> Map.Map Global (Set.Set Global) -> C.Term
zonk term sols eqs =
  run .
  runReader (NormContext (N.Env mempty mempty) mempty sols eqs mempty) $
  Norm.zonk term

readback :: N.Term -> C.Term
readback term =
  run .
  runReader (NormContext (N.Env mempty mempty) mempty mempty mempty mempty) $
  Norm.readback term

eval :: C.Term -> N.Term
eval term =
  run .
  runReader (NormContext (N.Env mempty mempty) mempty mempty mempty mempty) $
  Norm.eval term

infer :: String -> Text -> IO (Either String (QueryState, C.Term, C.Term))
infer fn s = parse prec0 fn s >>= traverse infer'

elaborate' :: S.TermAst -> IO (QueryState, C.Term)
elaborate' term = do
  (qs, term') <-
    liftIO .
    runState (QueryState mempty mempty 1000 mempty mempty mempty mempty mempty mempty mempty 2000 mempty) .
    runReader (QueryContext Nothing) .
    evalState ElabState .
    runReader (NormContext (N.Env mempty mempty) mempty mempty mempty mempty) .
    runReader (ElabContext mempty (initialPos "<TODO>") mempty False) $
    EE.check term N.ObjTypeType
  let
    term'' =
      run $
      runReader
        (NormContext
          (N.Env mempty mempty)
          mempty
          (justs $ unTypeUVs qs)
          mempty
          mempty)
      (Norm.eval term' >>= Norm.zonk)
  pure (qs, term'')

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
  ast <- parse toplevel f s
  traverse (\x -> swap <$> elaborate' x) ast
