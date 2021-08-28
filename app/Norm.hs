{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
-- {-# OPTIONS_GHC -fdefer-type-errors #-}

module Norm where

import Var
import qualified Core as C
import qualified Data.Map as Map
import Data.Maybe(fromJust)
import Debug.Trace
import Control.Monad.Reader
import qualified Data.Set as Set

data MetaEntry a = Solved a | Unsolved
  deriving Show

type StageMetas = Map.Map Global (MetaEntry C.Stage)
type Metas = Map.Map Global (MetaEntry Value)
type Locals = [Value]

type Spine = [Value]
data Closure = Closure [Value] C.Term
  deriving Show

-- type annotation
type Type = Value

data Value
  = Stuck Neutral
  | FunIntro Closure Type
  | FunType Type Closure
  | StagedElim Value Value C.Stage
  | StagedIntro Value Type C.Stage
  | StagedType Value C.Stage
  | TypeType
  | ElabError
  deriving Show

data Neutral
  = FlexVar Type Global Spine
  | RigidVar Type Level Spine
  deriving Show

type Norm a = Reader (Metas, Set.Set C.Stage, Locals) a

withLocals :: Norm a -> Locals -> Norm a
withLocals act locals = do
  (metas, stage, _) <- ask
  pure $ runReader act (metas, stage, locals)

pattern StuckFlexVar ty gl spine = Stuck (FlexVar ty gl spine)
pattern StuckRigidVar ty lv spine = Stuck (RigidVar ty lv spine)

appClosure :: Closure -> Value -> Norm Value
appClosure (Closure locals body) val = eval body `withLocals` (val:locals)

vApp :: Value -> Value -> Norm Value
vApp lam arg = case lam of
  FunIntro body vty -> appClosure body arg
  StuckFlexVar vty gl spine -> pure $ StuckFlexVar vty gl (arg:spine)
  StuckRigidVar vty lv spine -> pure $ StuckRigidVar vty lv (arg:spine)

vAppSpine :: Value -> Spine -> Norm Value
vAppSpine val spine = case spine of
  arg:spine -> do
    lam <- vAppSpine val spine
    vApp lam arg
  [] -> pure val

vAppBis :: Value -> [C.BinderInfo] -> Norm Value
vAppBis val bis = do
  (_, _, locals) <- ask
  case (locals, bis) of
    (local:locals, C.Abstract:bis) -> do
      lam <- vAppBis val bis
      vApp lam local
    (_:locals, C.Concrete:bis) -> vAppBis val bis
    (_, []) -> pure val
    _ -> error ("impossible\n" ++ show locals ++ "\n" ++ show bis)

vMeta :: Global -> Type -> Norm Value
vMeta gl vty = do
  (metas, _, _) <- ask
  pure $ case fromJust $ Map.lookup gl metas of
    Solved sol -> sol
    Unsolved -> StuckFlexVar vty gl []

subst :: C.Term -> Norm Value
subst trm = undefined

eval :: C.Term -> Norm Value
eval trm = do
  (_, stages, locals) <- ask
  case trm of
    C.Var ix _ -> pure $ locals !! unIndex ix
    C.TypeType -> pure TypeType
    C.FunIntro body tty -> FunIntro (Closure locals body) <$> eval tty
    C.FunType inTy outTy -> do
      vInTy <- eval inTy
      pure $ FunType vInTy (Closure locals outTy)
    C.FunElim lam arg -> eval lam >>= \lam -> vApp lam =<< eval arg
    C.StagedIntro inner ty s ->
      if Set.member s stages then
        eval inner
      else do
        vty <- eval ty
        vInner <- subst inner
        pure $ StagedIntro vInner vty s
    C.StagedType inner s -> (flip StagedType $ s) <$> eval inner
    C.StagedElim scr body s -> do
      vScr <- eval scr
      if Set.member s stages then
        eval body `withLocals` (vScr:locals)
      else do
        vBody <- subst body
        pure $ StagedElim vScr vBody s
    C.Let def _ body -> do
      vDef <- eval def
      eval body `withLocals` (vDef:locals)
    C.Meta gl tty -> vMeta gl =<< eval tty
    C.InsertedMeta bis gl tty -> (vMeta gl =<< eval tty) >>= \meta -> vAppBis meta bis
    C.ElabError -> pure ElabError

force :: Value -> Norm Value
force val = do
  (metas, _, _) <- ask
  case val of
    StuckFlexVar vty gl spine | Solved sol <- fromJust $ Map.lookup gl metas -> do
      sol <- vAppSpine sol spine
      force sol
    _ -> pure val

lvToIx :: Level -> Level -> Index
lvToIx lv1 lv2 = Index (unLevel lv1 - unLevel lv2 - 1)

readbackSpine :: Level -> C.Term -> Spine -> Norm C.Term
readbackSpine lv trm spine = case spine of
  arg:spine -> readbackSpine lv trm spine >>= \lam -> C.FunElim lam <$> readback lv arg
  [] -> pure trm

readback :: Level -> Value -> Norm C.Term
readback lv val = do
  val <- force val
  case val of
    StuckFlexVar vty gl spine -> readback lv vty >>= \vty -> readbackSpine lv (C.Meta gl vty) spine
    StuckRigidVar vty lv' spine -> readback lv vty >>= \vty -> readbackSpine lv (C.Var (lvToIx lv lv') vty) spine
    FunIntro body vty@(FunType inTy _) -> do
      body <- readback (Level $ unLevel lv + 1) =<< appClosure body (StuckRigidVar inTy lv [])
      C.FunIntro body <$> readback lv vty
    FunType inTy outTy ->
      (readback (Level $ unLevel lv + 1) =<< appClosure outTy (StuckRigidVar inTy lv [])) >>= \body -> C.FunType body <$> readback lv inTy
    StagedIntro inner ty s -> do
      cInner <- readback lv inner
      cTy <- readback lv ty
      pure $ C.StagedIntro cInner cTy s
    StagedType inner s -> (flip C.StagedType $ s) <$> readback lv inner
    StagedElim scr body s -> do
      cScr <- readback lv scr
      cBody <- readback (Level $ unLevel lv + 1) body
      pure $ C.StagedElim cScr cBody s
    TypeType -> pure C.TypeType
    ElabError -> pure C.ElabError