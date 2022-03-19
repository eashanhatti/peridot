module Codegen where

import Syntax.STG qualified as L
import Syntax.Object qualified as O
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Control.Carrier.State.Strict
import Control.Carrier.Reader
import Control.Algebra
import Normalization hiding(unTypeUVs, unStageUVs, unRepUVs, unUVEqs)
import Codegen.Stage(stage, StageState(StageState))
import Codegen.Lower
import Elaboration.Effect
import Elaboration
import Debug.Trace
import Data.Maybe
import Data.Map qualified as Map

stgify :: NormContext -> C.Term -> Maybe L.Term
stgify ctx term =
  let
    (oTerms :: [O.Term]) =
      evalState (StageState mempty mempty mempty 0 mempty) .
      runReader ctx $
      stage term
  in case oTerms of
    [oTerm] ->
      Just .
      run .
      evalState (LowerState mempty 0 mempty) .
      runReader (LowerContext mempty mempty mempty) $
      lower oTerm
    _ -> Nothing

stgifyFile :: String -> IO (Either String (Maybe L.Term))
stgifyFile f = do
  r <- elaborateFile' f
  case r of
    Right (qs, cTerm) ->
      let
        ctx =
          NormContext
            (N.Env mempty mempty)
            mempty
            (justs (unRepUVs qs))
            (justs (unTypeUVs qs))
            (unUVEqs qs)
      in pure (Right (stgify ctx cTerm))
    Left err -> pure (Left err)

justs = Map.map fromJust . Map.filter isJust
