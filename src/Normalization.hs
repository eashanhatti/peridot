module Normalization where

import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Extra
import Control.Monad
import Control.Effect.Reader
import Control.Effect.State
import Control.Algebra(Has)
import Data.Map(Map, (!))
import Data.Map qualified as Map
import Data.List(foldl')
import Data.Functor.Identity
import Numeric.Natural

data MetaEntry = Solved N.Term | Unsolved

data NormContext = NormContext N.Environment

data NormState = NormState (Map Global MetaEntry)

type Norm sig m =
  ( Has (Reader NormContext) sig m
  , Has (State NormState) sig m )

define :: Norm sig m => N.Term -> m a -> m a
define def = local (\(NormContext env) -> NormContext (N.withLocal def env))

closureOf :: Norm sig m => C.Term -> m N.Closure
closureOf term = do
  NormContext env <- ask
  pure (N.Closure env term)

appClosure :: Norm sig m => N.Closure -> N.Term -> m N.Term
appClosure (N.Closure env body) arg = do
  NormContext env <- ask
  local (const (NormContext (N.withLocal arg env))) (eval body)

evalClosure :: Norm sig m => N.Closure -> m N.Term
evalClosure clo = do
  NormContext env <- ask
  appClosure clo (N.FreeVar (fromIntegral (N.envSize env)))

definition :: C.Declaration -> C.Term
definition (C.MetaConstant did _) = C.MetaConstantIntro did
definition (C.ObjectConstant did _) = C.ObjectConstantIntro did
definition (C.Term _ _ def) = def
definition (C.Fresh _ _) = undefined
definition (C.DElabError) = error "FIXME"

eval :: Norm sig m => C.Term -> m N.Term
eval (C.FunType am inTy outTy) = N.FunType am <$> eval inTy <*> closureOf outTy
eval (C.FunIntro body) = N.FunIntro <$> closureOf body
eval (C.FunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  case vLam of
    N.FunIntro body -> appClosure body vArg
    _ -> pure (N.FunElim vLam vArg)
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
eval (C.IOIntro2 act k) = N.IOIntro2 <$> eval act <*> eval k

entry :: Norm sig m => Index -> m N.Term
entry ix = do
  NormContext env@(N.Env locals _) <- ask
  if fromIntegral ix > N.envSize env then
    pure (locals !! fromIntegral ix)
  else
    error "TODO"

type ShouldUnfold = Bool

readback :: Norm sig m => ShouldUnfold -> N.Term -> m C.Term
readback unf (N.FunType am inTy outTy) = C.FunType am <$> readback unf inTy <*> (evalClosure outTy >>= readback unf)
readback unf (N.FunIntro body) = C.FunIntro <$> (evalClosure body >>= readback unf)
readback unf (N.ObjectConstantIntro did) = pure (C.ObjectConstantIntro did)
readback unf (N.MetaConstantIntro did) = pure (C.MetaConstantIntro did)
readback unf (N.TypeType s) = pure (C.TypeType s)
readback unf (N.FreeVar (Level lvl)) = do
  NormContext env <- ask
  pure (C.LocalVar (Index (lvl - fromIntegral (N.envSize env) - 1)))
readback unf (N.FunElim lam arg) = C.FunElim <$> readback unf lam <*> readback unf arg
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
readback unf (N.IOIntro2 act k) = C.IOIntro2 <$> readback unf act <*> readback unf k

evalTop :: Norm sig m => N.Environment -> C.Term -> m N.Term
evalTop env term = local (const (NormContext env)) (eval term)

readbackWeak :: Norm sig m => N.Term -> m C.Term
readbackWeak = readback False

readbackFull :: Norm sig m => N.Term -> m C.Term
readbackFull = readback True

normalize :: Norm sig m => N.Term -> m N.Term
normalize = readbackFull >=> eval