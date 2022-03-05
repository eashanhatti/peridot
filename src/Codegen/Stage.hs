module Codegen.Stage where

import Syntax.Core qualified as C
import Syntax.Object qualified as O
import Syntax.Semantic qualified as N
import Syntax.Extra hiding(Stage)
import Control.Effect.NonDet
import Control.Effect.State
import Control.Effect.Throw
import Data.Map qualified as Map
import Data.Set qualified as Set
import Control.Algebra(Has)
import Normalization
import Unification
import Data.Maybe
import Control.Applicative
import Data.Foldable

data StageState = StageState
  { unSolutions :: (Map.Map Id (Maybe C.Term))
  , unRules :: [N.Term]
  , unLogvars :: Map.Map Global Id
  , unNextUV :: Global
  , unGlobals :: Map.Map Id C.Term }

type Stage sig m =
  ( Has NonDet sig m
  , Alternative m
  , Has (State StageState) sig m
  , Norm sig m )

stage :: Stage sig m => C.Term -> m O.Term
stage (C.FunType Explicit inTy outTy) = O.FunType <$> stage inTy <*> stage outTy
stage (C.FunIntro body) = O.FunIntro <$> stage body
stage (C.FunElim lam arg) = O.FunElim <$> stage lam <*> stage arg
stage (C.IOType ty) = O.IOType <$> stage ty
stage (C.IOIntro1 term) = O.IOIntro1 <$> stage term
stage (C.IOIntro2 act k) = O.IOIntro2 <$> stage act <*> stage k
stage (C.TypeType s) = pure (O.TypeType s)
stage (C.LocalVar ix) = pure (O.LocalVar ix)
stage (C.GlobalVar did) = do
  sols <- unSolutions <$> get
  case Map.lookup did sols of
    Just (Just term) -> stage term
    Just Nothing -> empty
    Nothing -> pure (O.GlobalVar did)
stage (C.Let decls body) = O.Let <$> fmap (map fromJust . filter isJust) (traverse stageDecl decls) <*> stage body

stageDecl :: Stage sig m => C.Declaration -> m (Maybe O.Declaration)
stageDecl (C.Fresh did _) = do
  state <- get
  put (state
    { unSolutions = Map.insert did Nothing (unSolutions state)
    , unNextUV = unNextUV state + 1
    , unGlobals = Map.insert did (C.UniVar (unNextUV state)) (unGlobals state)
    , unLogvars = Map.insert (unNextUV state) did (unLogvars state) })
  pure Nothing
stageDecl (C.Prove _ goal) = do
  globals <- unGlobals <$> get
  withGlobals (fmap ((,) (N.Env [] mempty)) globals) (eval goal >>= solve)
  pure Nothing
stageDecl (C.ObjectConstant did sig) = pure Nothing -- Just . O.ObjectConstant did <$> stage sig
stageDecl (C.MetaConstant did sig) = do
  state <- get
  vSig <- eval sig
  put (state { unRules = vSig:(unRules state) })
  pure Nothing
stageDecl (C.Term did sig def) = Just <$> (O.Term did <$> stage sig <*> stage def)

solve :: Stage sig m => N.Term -> m ()
solve goal = subgoals goal >>= traverse_ solve

subgoals :: Stage sig m => N.Term -> m [N.Term]
subgoals goal = do
  rules <- unRules <$> get
  rule <- oneOf rules
  case rule of
    N.FunType Implicit inTy outTy -> do
      sgs <- evalClosure outTy >>= subgoals
      pure (inTy:sgs)
    _ -> do
      r <- unify goal rule
      case r of
        Just subst -> do
          putSols (Map.toList (unTypeSols subst))
          pure []
        Nothing -> empty

putSols :: Stage sig m => [(Global, N.Term)] -> m ()
putSols [] = pure ()
putSols ((gl, sol):sols) = do
  state <- get
  cSol <- readbackWeak sol
  put (state { unSolutions = Map.insert (error "TODO") (Just cSol) (unSolutions state) })
  putSols sols
