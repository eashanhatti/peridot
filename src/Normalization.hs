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

data MetaEntry = Solved N.Term | Unsolved
  deriving (Show)

data NormContext = NormContext N.Environment
  deriving (Show)

data NormState = NormState (Map Global MetaEntry)
  deriving (Show)

type Norm sig m =
  ( Has (Reader NormContext) sig m
  , Has (State NormState) sig m )

bind :: HasCallStack => Norm sig m => m a -> m a
bind = local (\(NormContext env) -> NormContext (N.withLocal (N.FreeVar (fromIntegral (N.envSize env))) env))

define :: HasCallStack => Norm sig m => N.Term -> m a -> m a
define def = local (\(NormContext env) -> NormContext (N.withLocal def env))

closureOf :: HasCallStack => Norm sig m => C.Term -> m N.Closure
closureOf term = do
  NormContext env <- ask
  pure (N.Closure env term)

appClosure :: HasCallStack => Norm sig m => N.Closure -> N.Term -> m N.Term
appClosure (N.Closure env body) arg = local (const (NormContext (N.withLocal arg env))) (eval body)

evalClosure :: HasCallStack => Norm sig m => N.Closure -> m N.Term
evalClosure clo = do
  NormContext env <- ask
  appClosure clo (N.FreeVar (fromIntegral (N.envSize env)))

-- funIntros :: C.Term -> (C.Term -> C.Term)
-- funIntros (C.MetaFunType _ _ outTy) = C.MetaFunIntro . funIntros outTy
-- funIntros (C.ObjectFunType _ outTy) = C.ObjectFunIntro . funIntros outTy
-- funIntros _ = id

definition :: C.Declaration -> C.Term
definition (C.MetaConstant did sig) = undefined
definition (C.ObjectConstant did _ sig) = undefined
definition (C.Term _ _ _ def) = def
definition (C.Fresh _ _) = undefined
definition (C.DElabError) = error "FIXME"

eval :: HasCallStack => Norm sig m => C.Term -> m N.Term
eval (C.MetaFunType am inTy outTy) = N.MetaFunType am <$> eval inTy <*> closureOf outTy
eval (C.MetaFunIntro body) = N.MetaFunIntro <$> closureOf body
eval (C.ObjectFunType inTy outTy) = N.ObjectFunType <$> eval inTy <*> closureOf outTy
eval (C.ObjectFunIntro rep body) = N.ObjectFunIntro rep <$> closureOf body
eval (C.ObjectFunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  case vLam of
    N.ObjectFunIntro _ body -> appClosure body vArg
    _ -> pure (N.ObjectFunElim vLam vArg)
eval (C.MetaFunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  case vLam of
    N.MetaFunIntro body -> appClosure body vArg
    _ -> pure (N.MetaFunElim vLam vArg)
eval (C.Let decls body) = do
  NormContext (N.Env locals globals) <- ask
  let vDefs = Map.fromList ((map (\def -> (C.unId def, (N.Env locals (vDefs <> globals), definition def))) decls))
  local (const (NormContext (N.Env locals (globals <> vDefs)))) (eval body)
eval (C.MetaConstantIntro did) = pure (N.MetaConstantIntro did)
eval (C.ObjectConstantIntro did) = pure (N.ObjectConstantIntro did)
eval (C.TypeType s) = pure (N.TypeType s)
eval (C.LocalVar ix) = entry ix
eval (C.GlobalVar did) = do
  NormContext (N.Env _ ((! did) -> (env, term))) <- ask
  pure (N.TopVar did env term)
eval (C.UniVar gl) = pure (N.UniVar gl)
eval (C.IOType ty) = N.IOType <$> eval ty
eval (C.IOIntro1 term) = N.IOIntro1 <$> eval term
eval (C.IOIntro2 act k) = N.IOIntro2 act <$> eval k
eval C.UnitType = pure N.UnitType
eval C.UnitIntro = pure N.UnitIntro
eval C.EElabError = pure N.EElabError

entry :: HasCallStack => Norm sig m => Index -> m N.Term
entry ix = do
  NormContext (N.Env locals _) <- ask
  if fromIntegral ix >= length locals then
    error $ "`entry`:" ++ shower (ix, locals)
  else 
    pure (locals !! fromIntegral ix)

type ShouldUnfold = Bool

readback :: HasCallStack => Norm sig m => ShouldUnfold -> N.Term -> m C.Term
readback unf (N.MetaFunType am inTy outTy) = C.MetaFunType am <$> readback unf inTy <*> (evalClosure outTy >>= readback unf)
readback unf (N.MetaFunIntro body) = C.MetaFunIntro <$> (evalClosure body >>= readback unf)
readback unf (N.MetaFunElim lam arg) = C.MetaFunElim <$> readback unf lam <*> readback unf arg
readback unf (N.ObjectConstantIntro did) = pure (C.ObjectConstantIntro did)
readback unf (N.MetaConstantIntro did) = pure (C.MetaConstantIntro did)
readback unf (N.TypeType s) = pure (C.TypeType s)
readback unf (N.FreeVar (Level lvl)) = do
  NormContext env <- ask
  pure (C.LocalVar (Index (lvl - fromIntegral (N.envSize env) - 1)))
readback True (N.TopVar _ env def) = local (const (NormContext env)) (eval def) >>= readback False
readback False (N.TopVar did _ _) = pure (C.GlobalVar did)
readback True (N.UniVar gl) = do
  NormState metas <- get
  case metas ! gl of
    Solved sol -> readback True sol
    Unsolved -> pure (C.UniVar gl)
readback False (N.UniVar gl) = pure (C.UniVar gl)
readback unf (N.IOType ty) = C.IOType <$> readback unf ty
readback unf (N.IOIntro1 term) = C.IOIntro1 <$> readback unf term
readback unf (N.IOIntro2 act k) = C.IOIntro2 act <$> readback unf k
readback unf N.UnitType = pure C.UnitType
readback unf N.UnitIntro = pure C.UnitIntro
readback unf N.EElabError = pure C.EElabError

evalTop :: HasCallStack => Norm sig m => N.Environment -> C.Term -> m N.Term
evalTop env term = local (const (NormContext env)) (eval term)

readbackWeak :: HasCallStack => Norm sig m => N.Term -> m C.Term
readbackWeak = readback False

readbackFull :: HasCallStack => Norm sig m => N.Term -> m C.Term
readbackFull = readback True

normalize :: HasCallStack => Norm sig m => N.Term -> m N.Term
normalize = readbackFull >=> eval

withGlobals :: Norm sig m => Map Id (N.Environment, C.Term) -> m a -> m a
withGlobals globals =
  local (\(NormContext (N.Env locals globals')) -> NormContext (N.Env locals (globals <> globals')))
