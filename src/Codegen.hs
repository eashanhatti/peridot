module Codegen where

import Syntax.STG qualified as L
import Syntax.Object qualified as O
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Control.Carrier.State.Strict
import Control.Carrier.Reader
import Control.Algebra
import Normalization
import Codegen.Stage(stage, StageState(StageState), StageContext(StageContext))
import Codegen.Lower
import Elaboration.Effect(unTypeUVs, unStageUVs, unRepUVs)
import Elaboration
import Debug.Trace

stgify :: StageContext -> C.Term -> Maybe L.Term
stgify ctx term =
  let
    (oTerms :: [O.Term]) =
      evalState (StageState mempty mempty mempty 0 mempty) .
      runReader ctx .
      evalState (NormState mempty) .
      runReader (NormContext (N.Env mempty mempty)) $
      stage term
  in case oTerms of
    [oTerm] ->
      Just .
      run .
      evalState (LowerState mempty mempty mempty 0 mempty) .
      runReader (LowerContext mempty) $
      lower oTerm
    _ -> Nothing

stgifyFile :: String -> IO (Either String (Maybe L.Term))
stgifyFile f = do
  r <- elaborateFile' f
  case r of
    Right (qs, cTerm) ->
      let ctx = StageContext (unTypeUVs qs) (unStageUVs qs) (unRepUVs qs)
      in pure (Right (stgify ctx cTerm))
    Left err -> pure (Left err)
