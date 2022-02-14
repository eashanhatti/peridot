module Normalization where

import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Stage
import Syntax.Variable
import {-# SOURCE #-} Syntax.Telescope
import Control.Effect.Reader
import Control.Algebra(Has)
import Data.Map(Map)
import Data.Map qualified as Map
import Data.List(foldl')
import Data.Functor.Identity
import Numeric.Natural

data NormContext = NormContext N.Environment

type Norm sig m = Has (Reader NormContext) sig m

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

teleToType :: C.Telescope -> C.Term -> C.Term
teleToType tele outTy = foldl' (\outTy inTy -> C.FunType inTy outTy) outTy tele

definition :: C.Declaration -> C.Term
definition (C.Datatype _ tele _) = teleToType tele (C.TypeType Object) -- FIXME: `Object`
definition (C.Constr did tele _ _) =
  let vars = if size tele > 0 then map (C.LocalVar . Index) [size tele, size tele - 1 .. 0] else []
  in foldl' (\term _ -> C.FunIntro term) (C.DatatypeIntro did vars) vars
definition (C.Term _ _ def) = def

eval :: Norm sig m => C.Term -> m N.Term
eval (C.FunType inTy outTy) = N.FunType <$> eval inTy <*> closureOf outTy
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
eval (C.DatatypeIntro did args) = N.DatatypeIntro did <$> traverse eval args
eval (C.TypeType s) = pure (N.TypeType s)
eval (C.LocalVar ix) = entry ix
eval (C.UniVar gl) = pure (N.UniVar gl)

entry :: Norm sig m => Index -> m N.Term
entry ix = do
  NormContext env@(N.Env locals _) <- ask
  if fromIntegral ix > N.envSize env then
    pure (locals !! fromIntegral ix)
  else
    error "TODO"

type ShouldUnfold = Bool

readback :: Norm sig m => ShouldUnfold -> N.Term -> m C.Term
readback unf (N.FunType inTy outTy) = C.FunType <$> readback unf inTy <*> (evalClosure outTy >>= readback unf)
readback unf (N.FunIntro body) = C.FunIntro <$> (evalClosure body >>= readback unf)
readback unf (N.DatatypeIntro did args) = C.DatatypeIntro did <$> traverse (readback unf) args
readback unf (N.TypeType s) = pure (C.TypeType s)
readback unf (N.FreeVar (Level lvl)) = do
  NormContext env <- ask
  pure (C.LocalVar (Index (lvl - fromIntegral (N.envSize env) - 1)))
readback unf (N.UniVar gl) = pure (C.UniVar gl)
readback unf (N.FunElim lam arg) = C.FunElim <$> readback unf lam <*> readback unf arg
readback True (N.TopVar _ env def) = local (const (NormContext env)) (eval def) >>= readback True
readback False (N.TopVar did _ _) = pure (C.GlobalVar did)