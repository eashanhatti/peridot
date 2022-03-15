module Normalization where

import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Extra
import Control.Monad
import Control.Effect.Reader
import Control.Carrier.Reader
import Control.Effect.State
import Control.Carrier.State.Strict
import Control.Algebra(Has, run)
import Data.Map(Map)
import Data.Map qualified as Map
import Data.List(foldl')
import Data.Functor.Identity
import Numeric.Natural
import GHC.Stack
import Extra
import Shower
import Debug.Trace

data NormContext = NormContext
  { unEnv :: N.Environment
  , unTypeUVs :: Map Global (Maybe N.Term)
  , unStageUVs :: Map Global (Maybe N.Stage) }
  deriving (Show)

type Norm sig m =
  ( Has (Reader NormContext) sig m )

bind :: HasCallStack => Norm sig m => m a -> m a
bind = local (\ctx -> ctx { unEnv = N.withLocal (N.FreeVar (fromIntegral (N.envSize (unEnv ctx)))) (unEnv ctx) })

define :: HasCallStack => Norm sig m => N.Term -> m a -> m a
define def = local (\ctx -> ctx { unEnv = N.withLocal def (unEnv ctx) })

closureOf :: HasCallStack => Norm sig m => C.Term -> m N.Closure
closureOf term = do
  env <- unEnv <$> ask
  pure (N.Closure env term)

appClosure :: HasCallStack => Norm sig m => N.Closure -> N.Term -> m N.Term
appClosure (N.Closure env body) arg = local (\ctx -> ctx { unEnv = N.withLocal arg (unEnv ctx) }) (eval body)

evalClosure :: HasCallStack => Norm sig m => N.Closure -> m N.Term
evalClosure clo = do
  env <- unEnv <$> ask
  appClosure clo (N.FreeVar (fromIntegral (N.envSize env)))

funIntros :: C.Term -> (C.Term -> C.Term)
funIntros (C.FunType _ inTy outTy) = C.FunIntro inTy . funIntros outTy
funIntros _ = id

definition :: C.Declaration -> C.Term
definition (C.MetaConstant did sig) = funIntros sig (C.MetaConstantIntro did)
definition (C.ObjectConstant did sig) = funIntros sig (C.ObjectConstantIntro did)
definition (C.Term _ _ def) = def
definition (C.Fresh _ _) = undefined
definition (C.DElabError) = error "FIXME"

evalStage :: HasCallStack => Norm sig m => C.Stage -> m N.Stage
evalStage (C.Object rep) = N.Object <$> eval rep
evalStage C.Meta = pure N.Meta
evalStage (C.SUniVar gl) = pure (N.SUniVar gl)

eval :: HasCallStack => Norm sig m => C.Term -> m N.Term
eval (C.FunType am inTy outTy) = N.FunType am <$> eval inTy <*> closureOf outTy
eval (C.FunIntro ty body) = N.FunIntro <$> eval ty <*> closureOf body
eval (C.FunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  case vLam of
    N.FunIntro _ body -> appClosure body vArg
    _ -> pure (N.FunElim vLam vArg)
eval (C.Let decls body) = do
  N.Env locals globals <- unEnv <$> ask
  let vDefs = Map.fromList ((map (\def -> (C.unId def, (N.Env locals (vDefs <> globals), definition def))) decls))
  local (\ctx@(unEnv -> N.Env locals globals) -> ctx { unEnv = N.Env locals (globals <> vDefs) }) (eval body)
eval (C.MetaConstantIntro did) = pure (N.MetaConstantIntro did)
eval (C.ObjectConstantIntro did) = pure (N.ObjectConstantIntro did)
eval (C.TypeType s) = N.TypeType <$> evalStage s
eval (C.LocalVar ix) = entry ix
eval (C.GlobalVar did) = do
  N.Env _ ((! did) -> (env, term)) <- unEnv <$> ask
  pure (N.TopVar did env term)
eval (C.UniVar gl) = pure (N.UniVar gl)
eval (C.IOType ty) = N.IOType <$> eval ty
eval (C.IOIntroPure term) = N.IOIntro1 <$> eval term
eval (C.IOIntroBind act k) = N.IOIntro2 act <$> eval k
eval C.RepType = pure N.RepType
eval C.RepIntroPtr = pure N.RepIntroPtr
eval C.RepIntroLazy = pure N.RepIntroLazy
eval C.RepIntroWord = pure N.RepIntroWord
eval (C.RepIntroProd rs) = N.RepIntroProd <$> traverse eval rs
eval (C.RepIntroSum rs) = N.RepIntroSum <$> traverse eval rs
eval C.RepIntroErased = pure N.RepIntroErased
eval C.UnitType = pure N.UnitType
eval C.UnitIntro = pure N.UnitIntro
eval C.EElabError = pure N.EElabError

entry :: HasCallStack => Norm sig m => Index -> m N.Term
entry ix = do
  N.Env locals _ <- unEnv <$> ask
  if fromIntegral ix >= length locals then
    error $ "`entry`:" ++ shower (ix, locals)
  else 
    pure (locals !! fromIntegral ix)

type ShouldUnfold = Bool

readbackStage :: HasCallStack => Norm sig m => ShouldUnfold -> N.Stage -> m C.Stage
readbackStage unf (N.Object rep) = C.Object <$> readback unf rep
readbackStage unf N.Meta = pure C.Meta
readbackStage unf (N.SUniVar gl) = do
  metas <- unStageUVs <$> ask
  case metas ! gl of
    Just sol -> readbackStage True sol
    Nothing -> pure (C.SUniVar gl)

readback :: HasCallStack => Norm sig m => ShouldUnfold -> N.Term -> m C.Term
readback unf (N.FunType am inTy outTy) = C.FunType am <$> readback unf inTy <*> (evalClosure outTy >>= readback unf)
readback unf (N.FunIntro ty body) = C.FunIntro <$> readback unf ty <*> (evalClosure body >>= readback unf)
readback unf (N.ObjectConstantIntro did) = pure (C.ObjectConstantIntro did)
readback unf (N.MetaConstantIntro did) = pure (C.MetaConstantIntro did)
readback unf (N.TypeType s) = C.TypeType <$> readbackStage unf s
readback unf (N.FreeVar (Level lvl)) = do
  env <- unEnv <$> ask
  pure (C.LocalVar (Index (lvl - fromIntegral (N.envSize env) - 1)))
readback unf (N.FunElim lam arg) = C.FunElim <$> readback unf lam <*> readback unf arg
readback True (N.TopVar _ env def) = local (\ctx -> ctx { unEnv = env }) (eval def) >>= readback False
readback False (N.TopVar did _ _) = pure (C.GlobalVar did)
readback True (N.UniVar gl) = do
  metas <- unTypeUVs <$> ask
  case metas ! gl of
    Just sol -> readback True sol
    Nothing -> pure (C.UniVar gl)
readback False (N.UniVar gl) = pure (C.UniVar gl)
readback unf (N.IOType ty) = C.IOType <$> readback unf ty
readback unf (N.IOIntro1 term) = C.IOIntroPure <$> readback unf term
readback unf (N.IOIntro2 act k) = C.IOIntroBind act <$> readback unf k
readback unf N.RepType = pure C.RepType
readback unf N.RepIntroPtr = pure C.RepIntroPtr
readback unf N.RepIntroLazy = pure C.RepIntroLazy
readback unf N.RepIntroWord = pure C.RepIntroWord
readback unf (N.RepIntroProd rs) = C.RepIntroProd <$> traverse (readback unf) rs
readback unf (N.RepIntroSum rs) = C.RepIntroSum <$> traverse (readback unf) rs
readback unf N.RepIntroErased = pure C.RepIntroErased
readback unf N.UnitType = pure C.UnitType
readback unf N.UnitIntro = pure C.UnitIntro
readback unf N.EElabError = pure C.EElabError

evalTop :: HasCallStack => Norm sig m => N.Environment -> C.Term -> m N.Term
evalTop env term = local (\ctx -> ctx { unEnv = env }) (eval term)

readbackWeak :: HasCallStack => Norm sig m => N.Term -> m C.Term
readbackWeak = readback False

readbackFull :: HasCallStack => Norm sig m => N.Term -> m C.Term
readbackFull = readback True

normalize :: HasCallStack => Norm sig m => N.Term -> m N.Term
normalize = readbackFull >=> eval

normalizeStage :: HasCallStack => Norm sig m => N.Stage -> m N.Stage
normalizeStage = readbackStage True >=> evalStage

withGlobals :: Norm sig m => Map Id (N.Environment, C.Term) -> m a -> m a
withGlobals globals =
  local (\ctx@(unEnv -> (N.Env locals globals')) -> ctx { unEnv = N.Env locals (globals <> globals') })
