module Normalization where

import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Common
import Control.Monad
import Control.Effect.Reader
import Control.Carrier.Reader
import Control.Effect.State
import Control.Carrier.State.Strict
import Control.Algebra(Has, run)
import Data.Set qualified as Set
import Data.Map qualified as Map
import Data.Foldable
import Data.Functor.Identity
import Numeric.Natural
import GHC.Stack
import Extra
import Shower
import Debug.Trace
import Data.Sequence hiding(length)
import Prelude hiding(length)

data NormContext = NormContext
  { unEnv :: N.Environment
  , unVisited :: Set.Set Global
  , unTypeUVs :: Map.Map Global N.Term
  , unVCUVs :: Map.Map Global N.ValueCategory
  , unUVEqs :: Map.Map Global Global } -- FIXME? `Map Global (Set Global)`
  deriving (Show)

type Norm sig m =
  ( Has (Reader NormContext) sig m )

bind :: HasCallStack => Norm sig m => m a -> m a
bind = local (\ctx -> ctx { unEnv = N.withLocal (N.LocalVar (fromIntegral (N.envSize (unEnv ctx)))) (unEnv ctx) })

define :: HasCallStack => Norm sig m => N.Term -> m a -> m a
define def = local (\ctx -> ctx { unEnv = N.withLocal def (unEnv ctx) })

closureOf :: HasCallStack => Norm sig m => C.Term -> m N.Closure
closureOf term = do
  env <- unEnv <$> ask
  pure (N.Clo env term)

appClosure :: HasCallStack => Norm sig m => N.Closure -> N.Term -> m N.Term
appClosure (N.Clo env body) arg = local (\ctx -> ctx { unEnv = N.withLocal arg env }) (eval body)

evalClosure :: HasCallStack => Norm sig m => N.Closure -> m N.Term
evalClosure clo = do
  env <- unEnv <$> ask
  appClosure clo (N.LocalVar (fromIntegral (N.envSize env)))

funIntros :: C.Term -> (C.Term -> C.Term)
funIntros (C.MetaFunType _ _ outTy) = C.MetaFunIntro . funIntros outTy
funIntros (C.ObjFunType _ outTy) = C.ObjFunIntro . funIntros outTy
funIntros _ = id

delay :: Norm sig m => ReaderC NormContext Identity a -> m a
delay act = do
  ctx <- ask
  pure (run . runReader ctx $ act)

definition :: C.Declaration -> C.Term
definition (C.MetaConst did sig) = funIntros sig (C.Rigid (C.MetaConstIntro did))
definition (C.ObjConst did sig) = funIntros sig (C.Rigid (C.ObjConstIntro did))
definition (C.ObjTerm _ _ def) = def
definition (C.MetaTerm _ _ def) = def
definition (C.Fresh _ _) = undefined
definition (C.DElabError) = error "FIXME"

eval :: HasCallStack => Norm sig m => C.Term -> m N.Term
eval (C.MetaFunType am inTy outTy) = N.MetaFunType am <$> eval inTy <*> closureOf outTy
eval (C.MetaFunIntro body) = N.MetaFunIntro <$> closureOf body
eval (C.ObjFunType inTy outTy) = N.ObjFunType <$> eval inTy <*> closureOf outTy
eval (C.ObjFunIntro body) = N.ObjFunIntro <$> closureOf body
eval (C.ObjFunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  reded <- delay case vLam of
    N.ObjFunIntro body -> Just <$> appClosure body vArg
    _ -> pure Nothing
  pure (N.Neutral reded (N.ObjFunElim vLam vArg))
eval (C.MetaFunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  reded <- delay case vLam of
    N.MetaFunIntro body -> Just <$> appClosure body vArg
    _ -> pure Nothing
  pure (N.Neutral reded (N.MetaFunElim vLam vArg))
-- eval (C.Let decls body) = do
--   N.Env locals globals <- unEnv <$> ask
--   let vDefs = foldl' (\acc def -> Map.insert (C.unId def) (N.Env locals (vDefs <> globals), definition def) acc) mempty decls
--   local (\ctx -> ctx { unEnv = N.Env locals (globals <> vDefs) }) (eval body)
eval (C.TypeType (C.SUniVar gl)) = undefined -- FIXME?
eval (C.TypeType C.Meta) = pure (N.TypeType N.Meta)
eval (C.TypeType C.Obj) = pure (N.TypeType N.Obj)
eval (C.TypeType (C.Low l)) = pure (N.TypeType (N.Low l))
eval (C.LocalVar ix) = entry ix
eval (C.GlobalVar did) = do
  N.Env _ ((! did) -> term) <- unEnv <$> ask
  pure (N.Neutral (Just term) (N.GlobalVar did))
eval (C.UniVar gl) = do
  reded <- delay do
    visited <- unVisited <$> ask
    if Set.member gl visited then
      pure Nothing
    else do
      uvs <- unTypeUVs <$> ask
      case Map.lookup gl uvs of
        Just sol -> pure (Just sol)
        Nothing -> do
          eqs <- unUVEqs <$> ask
          case Map.lookup gl eqs of
            Just gl' -> Just <$> eval (C.UniVar gl')
            Nothing -> pure Nothing
  pure (N.Neutral reded (N.UniVar gl))
eval (C.CodeCoreElim term) = do
  term' <- eval term
  reded <- pure case term' of
    N.Rigid (N.CodeCoreIntro code) -> Just code
    _ -> Nothing
  pure (N.Neutral reded (N.CodeCoreElim term'))
eval (C.CodeLowCTmElim term) = do
  term' <- eval term
  reded <- pure case term' of
    N.Rigid (N.CodeLowCTmIntro code) -> Just code
    _ -> Nothing
  pure (N.Neutral reded (N.CodeLowCTmElim term'))
eval (C.Rigid rterm) = N.Rigid <$> traverse eval rterm

entry :: HasCallStack => Norm sig m => Index -> m N.Term
entry ix = do
  N.Env locals _ <- unEnv <$> ask
  if fromIntegral ix >= length locals then
    error $ "`entry`:" ++ shower (ix, locals)
  else 
    pure (locals `index` fromIntegral ix)

type ShouldZonk = Bool

readback' :: HasCallStack => Norm sig m => ShouldZonk -> N.Term -> m C.Term
readback' opt (N.MetaFunType am inTy outTy) = C.MetaFunType am <$> readback' opt inTy <*> (evalClosure outTy >>= readback' opt)
readback' opt (N.MetaFunIntro body) = C.MetaFunIntro <$> (evalClosure body >>= readback' opt)
readback' opt (N.ObjFunType inTy outTy) =
  C.ObjFunType <$> readback' opt inTy <*> (evalClosure outTy >>= readback' opt)
readback' opt (N.ObjFunIntro body) = C.ObjFunIntro <$> (evalClosure body >>= readback' opt)
readback' opt (N.TypeType (N.SUniVar gl)) = undefined -- FIXME?
readback' opt (N.TypeType (N.Low l)) = pure (C.TypeType (C.Low l))
readback' opt (N.TypeType N.Meta) = pure (C.TypeType C.Meta)
readback' opt (N.TypeType N.Obj) = pure (C.TypeType C.Obj)
readback' opt (N.LocalVar (Level lvl)) = do
  env <- unEnv <$> ask
  pure (C.LocalVar (Index (lvl - fromIntegral (N.envSize env) - 1)))
readback' True (N.Neutral (Just sol) (N.UniVar _)) = readback' True sol
readback' opt (N.Neutral _ redex) = readbackRedex opt redex
readback' opt (N.Rigid rterm) = C.Rigid <$> traverse (readback' opt) rterm

readbackRedex :: HasCallStack => Norm sig m => ShouldZonk -> N.Redex -> m C.Term
readbackRedex opt (N.MetaFunElim lam arg) = C.MetaFunElim <$> readback' opt lam <*> readback' opt arg
readbackRedex opt (N.ObjFunElim lam arg) = C.ObjFunElim <$> readback' opt lam <*> readback' opt arg
readbackRedex opt (N.CodeCoreElim quote) = C.CodeCoreElim <$> readback' opt quote
readbackRedex opt (N.CodeLowCTmElim quote) = C.CodeLowCTmElim <$> readback' opt quote
readbackRedex opt (N.GlobalVar did) = pure (C.GlobalVar did)
readbackRedex opt (N.UniVar gl) = pure (C.UniVar gl)

readback :: HasCallStack => Norm sig m => N.Term -> m C.Term
readback = readback' False

zonk :: HasCallStack => Norm sig m => N.Term -> m C.Term
zonk = readback' True

-- normalize :: HasCallStack => Norm sig m => N.Term -> m N.Term
-- normalize = readbackFull >=> eval

-- withGlobals :: Norm sig m => Map.Map Id (N.Environment, C.Term) -> m a -> m a
-- withGlobals globals =
--   local (\ctx@(unEnv -> N.Env locals globals') -> ctx { unEnv = N.Env locals (globals <> globals') })
