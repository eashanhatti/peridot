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
import Data.Set qualified as Set
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

data NormContext = NormContext
  { unEnv :: N.Environment
  , unVisited :: Set.Set Global
  , unTypeUVs :: Map.Map Global N.Term
  , unUVEqs :: Map.Map Global Global } -- FIXME? `Map Global (Set Global)`
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
appClosure (N.Closure env body) arg = local (\ctx -> ctx { unEnv = N.withLocal arg env }) (eval body)

evalClosure :: HasCallStack => Norm sig m => N.Closure -> m N.Term
evalClosure clo = do
  env <- unEnv <$> ask
  appClosure clo (N.FreeVar (fromIntegral (N.envSize env)))

funIntros :: C.Term -> (C.Term -> C.Term)
funIntros (C.MetaFunType _ _ outTy) = C.MetaFunIntro . funIntros outTy
funIntros (C.ObjectFunType _ outTy) = C.ObjectFunIntro . funIntros outTy
funIntros _ = id

definition :: C.Declaration -> C.Term
definition (C.MetaConstant did sig) = funIntros sig (C.MetaConstantIntro did)
definition (C.ObjectConstant did sig) = funIntros sig (C.ObjectConstantIntro did)
definition (C.Term _ _ def) = def
definition (C.Fresh _ _) = undefined
definition (C.DElabError) = error "FIXME"

eval :: HasCallStack => Norm sig m => C.Term -> m N.Term
eval (C.QuoteType quote) = N.QuoteType <$> traverse eval quote
eval (C.QuoteIntro quote) = N.QuoteIntro <$> traverse eval quote
eval (C.MetaFunType am inTy outTy) = N.MetaFunType am <$> eval inTy <*> closureOf outTy
eval (C.MetaFunIntro body) = N.MetaFunIntro <$> closureOf body
eval (C.ObjectFunType inTy outTy) = N.ObjectFunType <$> eval inTy <*> closureOf outTy
eval (C.ObjectFunIntro body) = N.ObjectFunIntro <$> closureOf body
eval (C.ObjectFunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  case vLam of
    N.ObjectFunIntro body -> appClosure body vArg
    _ -> pure (N.ObjectFunElim vLam vArg)
eval (C.MetaFunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  case vLam of
    N.MetaFunIntro body -> appClosure body vArg
    _ -> pure (N.MetaFunElim vLam vArg)
eval (C.Let decls body) = do
  N.Env locals globals <- unEnv <$> ask
  let vDefs = Map.fromList ((map (\def -> (C.unId def, (N.Env locals (vDefs <> globals), definition def))) decls))
  local (\ctx -> ctx { unEnv = N.Env locals (globals <> vDefs) }) (eval body)
eval (C.MetaConstantIntro did) = pure (N.MetaConstantIntro did)
eval (C.ObjectConstantIntro did) = pure (N.ObjectConstantIntro did)
eval (C.TypeType s) = pure (N.TypeType s)
eval (C.LocalVar ix) = entry ix
eval (C.GlobalVar did) = do
  N.Env _ ((! did) -> (env, term)) <- unEnv <$> ask
  pure (N.TopVar did env term)
eval (C.UniVar gl) = pure (N.UniVar gl)
eval (C.IOType ty) = N.IOType <$> eval ty
eval (C.IOIntroPure term) = N.IOIntroPure <$> eval term
eval (C.IOIntroBind act k) = N.IOIntroBind act <$> eval k
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

readback :: HasCallStack => Norm sig m => ShouldUnfold -> N.Term -> m C.Term
readback unf (N.QuoteType quote) = C.QuoteType <$> traverse (readback unf) quote
readback unf (N.QuoteIntro quote) = C.QuoteIntro <$> traverse (readback unf) quote
readback unf (N.MetaFunType am inTy outTy) = C.MetaFunType am <$> readback unf inTy <*> (evalClosure outTy >>= readback unf)
readback unf (N.MetaFunIntro body) = C.MetaFunIntro <$> (evalClosure body >>= readback unf)
readback unf (N.MetaFunElim lam arg) = C.MetaFunElim <$> readback unf lam <*> readback unf arg
readback unf (N.ObjectFunType inTy outTy) =
  C.ObjectFunType <$> readback unf inTy <*> (evalClosure outTy >>= readback unf)
readback unf (N.ObjectFunIntro body) = C.ObjectFunIntro <$> (evalClosure body >>= readback unf)
readback unf (N.ObjectFunElim lam arg) = C.ObjectFunElim <$> readback unf lam <*> readback unf arg
readback unf (N.ObjectConstantIntro did) = pure (C.ObjectConstantIntro did)
readback unf (N.MetaConstantIntro did) = pure (C.MetaConstantIntro did)
readback unf (N.TypeType s) = pure (C.TypeType s)
readback unf (N.FreeVar (Level lvl)) = do
  env <- unEnv <$> ask
  pure (C.LocalVar (Index (lvl - fromIntegral (N.envSize env) - 1)))
readback True (N.TopVar _ env def) = local (\ctx -> ctx { unEnv = env }) (eval def) >>= readback False
readback False (N.TopVar did _ _) = pure (C.GlobalVar did)
readback True (N.UniVar gl) = do
  visited <- unVisited <$> ask
  if Set.member gl visited then
    pure (C.UniVar gl)
  else do
    uvs <- unTypeUVs <$> ask
    case Map.lookup gl uvs of
      Just sol -> local (\ctx -> ctx { unVisited = Set.insert gl (unVisited ctx) }) (readback True sol)
      Nothing -> do
        eqs <- unUVEqs <$> ask
        case Map.lookup gl eqs of
          Just gl' -> readback True (N.UniVar gl')
          Nothing -> pure (C.UniVar gl)
readback False (N.UniVar gl) = pure (C.UniVar gl)
readback unf (N.IOType ty) = C.IOType <$> readback unf ty
readback unf (N.IOIntroPure term) = C.IOIntroPure <$> readback unf term
readback unf (N.IOIntroBind act k) = C.IOIntroBind act <$> readback unf k
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

withGlobals :: Norm sig m => Map.Map Id (N.Environment, C.Term) -> m a -> m a
withGlobals globals =
  local (\ctx@(unEnv -> N.Env locals globals') -> ctx { unEnv = N.Env locals (globals <> globals') })
