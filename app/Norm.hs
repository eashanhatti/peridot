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
  | StagedElim Value C.Term C.Stage
  | StagedIntro C.Term Type C.Stage
  | StagedType Value C.Stage
  | TypeType
  | ElabError
  deriving Show

data Neutral
  = FlexVar Type Global Spine
  | RigidVar Type Level Spine
  deriving Show

type Norm a = Reader (Level, Metas, Set.Set C.Stage, Locals) a

pattern StuckFlexVar ty gl spine = Stuck (FlexVar ty gl spine)
pattern StuckRigidVar ty lv spine = Stuck (RigidVar ty lv spine)

appClosure :: Closure -> Value -> Norm Value
appClosure (Closure locals body) val = define val $ eval body

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
  (_, _, _, locals) <- ask
  case (locals, bis) of
    (local:locals, C.Abstract:bis) -> do
      lam <- vAppBis val bis
      vApp lam local
    (_:locals, C.Concrete:bis) -> vAppBis val bis
    (_, []) -> pure val
    _ -> error ("impossible\n" ++ show locals ++ "\n" ++ show bis)

vMeta :: Global -> Type -> Norm Value
vMeta gl vty = do
  (_, metas, _, _) <- ask
  pure $ case fromJust $ Map.lookup gl metas of
    Solved sol -> sol
    Unsolved -> StuckFlexVar vty gl []

bind :: Value -> Norm a -> Norm a
bind ty act = do
  (level, metas, stages, locals) <- ask
  pure $ runReader act (incLevel level, metas, stages, (StuckRigidVar ty level []):locals)

define :: Value -> Norm a -> Norm a
define val act = do
  (level, metas, stages, locals) <- ask
  pure $ runReader act (incLevel level, metas, stages, val:locals)

inc :: Norm a -> Norm a
inc act = do
  (level, metas, stages, locals) <- ask
  pure $ runReader act (incLevel level, metas, stages, locals)

subst :: C.Term -> Norm C.Term
subst trm = do
  (_, _, stages, locals) <- ask
  case trm of
    C.FunIntro body ty@(C.FunType inTy _) -> do
      vInTy <- eval ty
      C.FunIntro <$> bind vInTy (subst body) <*> subst ty
    C.FunType inTy outTy -> do
      vInTy <- eval inTy
      C.FunType <$> subst inTy <*> bind vInTy (subst outTy)
    C.FunElim lam arg -> C.FunElim <$> subst lam <*> subst arg
    C.StagedIntro inner ty s ->
      if Set.member s stages then
        C.Value <$> eval inner
      else
        C.StagedIntro <$> subst inner <*> subst ty <*> pure s
    C.StagedType inner s -> C.StagedType <$> subst inner <*> pure s
    C.StagedElim scr body s ->
      if Set.member s stages then do
        vScr <- eval scr
        C.Value <$> define vScr (eval body)
      else
        C.StagedElim <$> subst scr <*> subst body <*> pure s
    C.Let def defTy body -> do
      vDefTy <- eval defTy
      C.Let <$> subst def <*> subst defTy <*> bind vDefTy (subst body)
    C.Meta gl tty -> C.Meta <$> pure gl <*> subst tty
    C.InsertedMeta bis gl tty -> C.InsertedMeta <$> pure bis <*> pure gl <*> subst tty
    _ -> pure trm

eval :: C.Term -> Norm Value
eval trm = do
  (_, _, stages, locals) <- ask
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
        inner <- subst inner
        pure $ StagedIntro inner vty s
    C.StagedType inner s -> (flip StagedType $ s) <$> eval inner
    C.StagedElim scr body s -> do
      vScr <- eval scr
      if Set.member s stages then
        define vScr $ eval body
      else do
        body <- subst body
        pure $ StagedElim vScr body s
    C.Let def _ body -> do
      vDef <- eval def
      define vDef $ eval body
    C.Meta gl tty -> vMeta gl =<< eval tty
    C.InsertedMeta bis gl tty -> (vMeta gl =<< eval tty) >>= \meta -> vAppBis meta bis
    C.ElabError -> pure ElabError

force :: Value -> Norm Value
force val = do
  (_, metas, _, _) <- ask
  case val of
    StuckFlexVar vty gl spine | Solved sol <- fromJust $ Map.lookup gl metas -> do
      sol <- vAppSpine sol spine
      force sol
    _ -> pure val

lvToIx :: Level -> Level -> Index
lvToIx lv1 lv2 = Index (unLevel lv1 - unLevel lv2 - 1)

readbackSpine :: C.Term -> Spine -> Norm C.Term
readbackSpine trm spine = do
  (lv, _, _, _) <- ask
  case spine of
    arg:spine -> C.FunElim <$> readbackSpine trm spine <*> readback arg
    -- readbackSpine trm spine >>= \lam -> C.FunElim lam <$> readback lv arg
    [] -> pure trm

readbackTerm :: C.Term -> Norm C.Term
readbackTerm trm = case trm of
  C.FunIntro body ty@(C.FunType inTy _) -> C.FunIntro <$> inc (readbackTerm body) <*> readbackTerm ty
  C.FunType inTy outTy -> C.FunType <$> readbackTerm inTy <*> inc (readbackTerm outTy)
  C.FunElim lam arg -> C.FunElim <$> readbackTerm lam <*> readbackTerm arg
  C.StagedIntro inner ty s -> C.StagedIntro <$> readbackTerm inner <*> readbackTerm ty <*> pure s
  C.StagedType inner s -> C.StagedType <$> readbackTerm inner <*> pure s
  C.StagedElim scr body s -> C.StagedElim <$> readbackTerm scr <*> inc (readbackTerm body) <*> pure s
  C.Let def defTy body -> C.Let <$> readbackTerm def <*> readbackTerm defTy <*> inc (readbackTerm body)
  C.Meta gl ty -> C.Meta <$> pure gl <*> readbackTerm ty
  C.InsertedMeta bis gl ty -> C.InsertedMeta <$> pure bis <*> pure gl <*> readbackTerm ty
  C.Value val -> readback val
  _ -> pure trm

readback :: Value -> Norm C.Term
readback val = do
  val <- force val
  case val of
    StuckFlexVar vty gl spine -> do
      meta <- C.Meta <$> pure gl <*> readback vty
      readbackSpine meta spine
    StuckRigidVar vty lv' spine -> do
      (lv, _, _, _) <- ask
      var <- C.Var <$> pure (lvToIx lv lv') <*> readback vty
      readbackSpine var spine
    FunIntro body vty@(FunType inTy _) -> do
      (lv, _, _, _) <- ask
      vBody <- appClosure body (StuckRigidVar inTy lv [])
      C.FunIntro <$> readback vBody <*> readback vty
    FunType inTy outTy -> do
      (lv, _, _, _) <- ask
      vOutTy <- appClosure outTy (StuckRigidVar inTy lv [])
      C.FunType <$> readback inTy <*> bind inTy (readback vOutTy)
    StagedIntro inner ty s -> C.StagedIntro <$> readbackTerm inner <*> readback ty <*> pure s
    StagedType inner s -> C.StagedType <$> readback inner <*> pure s
    StagedElim scr body s -> C.StagedElim <$> readback scr <*> readbackTerm body <*> pure s
    TypeType -> pure C.TypeType
    ElabError -> pure C.ElabError