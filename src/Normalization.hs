module Normalization where

import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Variable
import Control.Effect.Reader
import Control.Algebra(Has)
import Data.Map(Map)
import Data.Map qualified as Map
import Data.Functor.Identity
import Numeric.Natural

data NormContext = NormContext Level [N.Term]

type Norm sig m = Has (Reader NormContext) sig m

closureOf :: Norm sig m => C.Term -> m N.Closure
closureOf term = do
  NormContext _ env <- ask
  pure (N.Closure env term)

appClosure :: Norm sig m => N.Closure -> N.Term -> m N.Term
appClosure (N.Closure env body) arg = do
  NormContext lvl env <- ask
  local (const (NormContext (lvl + 1) (arg:env))) (eval body)

evalClosure :: Norm sig m => N.Closure -> m N.Term
evalClosure clo = do
  NormContext lvl _ <- ask
  appClosure clo (N.FreeVar lvl)

eval :: Norm sig m => C.Term -> m N.Term
eval (C.FunType inTy outTy) = N.FunType <$> eval inTy <*> closureOf outTy
eval (C.FunIntro body) = N.FunIntro <$> closureOf body
eval (C.FunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  case vLam of
    N.FunIntro body -> appClosure body vArg
    _ -> pure (N.StuckFunElim vLam vArg)
eval (C.DatatypeIntro did args) = N.DatatypeIntro did <$> traverse eval args
eval (C.TypeType s) = pure (N.TypeType s)
eval (C.Var ix) = do
  NormContext _ env <- ask
  entry ix
eval (C.UniVar gl) = pure (N.UniVar gl)

entry :: Norm sig m => Index -> m N.Term
entry ix = do
  NormContext _ env <- ask
  if fromIntegral ix > length env then
    pure (env !! fromIntegral ix)
  else
    error "TODO"

readback :: Norm sig m => N.Term -> m C.Term
readback (N.FunType inTy outTy) = C.FunType <$> readback inTy <*> (evalClosure outTy >>= readback)
readback (N.FunIntro body) = C.FunIntro <$> (evalClosure body >>= readback)
readback (N.DatatypeIntro did args) = C.DatatypeIntro did <$> traverse readback args
readback (N.TypeType s) = pure (C.TypeType s)
readback (N.FreeVar (Level lvl)) = do
  NormContext (Level lvl') _ <- ask
  pure (C.Var (Index (lvl - lvl' - 1)))
readback (N.UniVar gl) = pure (C.UniVar gl)
readback (N.StuckFunElim lam arg) = C.FunElim <$> readback lam <*> readback arg


bind :: Norm sig m => Natural -> m a -> m a
bind n = local (\(NormContext lvl env) -> NormContext (lvl + Level n) (env ++ [N.FreeVar vlvl | vlvl <- [lvl + 1 .. Level n]]))