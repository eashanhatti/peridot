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

data NormContext = NormContext [N.Definition]

type Norm sig m = Has (Reader NormContext) sig m

define :: Norm sig m => N.Term -> m a -> m a
define def = local (\(NormContext env) -> NormContext (N.Simple def : env))

closureOf :: Norm sig m => C.Term -> m N.Closure
closureOf term = do
  NormContext env <- ask
  pure (N.Closure env term)

appClosure :: Norm sig m => N.Closure -> N.Term -> m N.Term
appClosure (N.Closure env body) arg = do
  NormContext env <- ask
  local (const (NormContext (N.Simple arg : env))) (eval body)

evalClosure :: Norm sig m => N.Closure -> m N.Term
evalClosure clo = do
  NormContext env <- ask
  appClosure clo (N.FreeVar (fromIntegral (length env)))

teleToType :: C.Telescope -> C.Term -> C.Term
teleToType tele outTy = foldl' (\outTy inTy -> C.FunType inTy outTy) outTy tele

definition :: C.Declaration -> C.Term
definition (C.Datatype _ tele _) = teleToType tele (C.TypeType Object)
definition (C.Constr did tele _ _) =
  let vars = if size tele > 0 then map (C.Var . Index) [size tele, size tele - 1 .. 0] else []
  in foldl' (\term _ -> C.FunIntro term) (C.DatatypeIntro did vars) vars
definition (C.Term _ def) = def

eval :: Norm sig m => C.Term -> m N.Term
eval (C.FunType inTy outTy) = N.FunType <$> eval inTy <*> closureOf outTy
eval (C.FunIntro body) = N.FunIntro <$> closureOf body
eval (C.FunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  case vLam of
    N.FunIntro body -> appClosure body vArg
    _ -> pure (N.StuckFunElim vLam vArg)
eval (C.Let decls body) = do
  NormContext env <- ask
  let vDefs = map (\def -> N.Recursive (reverse vDefs ++ env) (definition def)) decls
  local (\(NormContext env) -> NormContext (reverse vDefs ++ env)) (eval body)
eval (C.DatatypeIntro did args) = N.DatatypeIntro did <$> traverse eval args
eval (C.TypeType s) = pure (N.TypeType s)
eval (C.Var ix) = entry ix
eval (C.UniVar gl) = pure (N.UniVar gl)

entry :: Norm sig m => Index -> m N.Term
entry ix = do
  NormContext env <- ask
  if fromIntegral ix > length env then
    case env !! fromIntegral ix of
      N.Simple def -> pure def
      N.Recursive env def -> local (const (NormContext env)) (eval def)
  else
    error "TODO"

readback :: Norm sig m => N.Term -> m C.Term
readback (N.FunType inTy outTy) = C.FunType <$> readback inTy <*> (evalClosure outTy >>= readback)
readback (N.FunIntro body) = C.FunIntro <$> (evalClosure body >>= readback)
readback (N.DatatypeIntro did args) = C.DatatypeIntro did <$> traverse readback args
readback (N.TypeType s) = pure (C.TypeType s)
readback (N.FreeVar (Level lvl)) = do
  NormContext env <- ask
  pure (C.Var (Index (lvl - fromIntegral (length env) - 1)))
readback (N.UniVar gl) = pure (C.UniVar gl)
readback (N.StuckFunElim lam arg) = C.FunElim <$> readback lam <*> readback arg