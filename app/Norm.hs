{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
-- {-# OPTIONS_GHC -fdefer-type-errors #-}

module Norm where

import Var
import qualified Core as C
import qualified Data.Map as Map
import Data.Maybe(fromJust)
import Debug.Trace
import Control.Monad.Reader
import qualified Data.Set as Set
import GHC.Stack
import Data.List(intersperse)

data MetaEntry a = Solved a | Unsolved
  deriving Show

type Metas = Map.Map Global (MetaEntry Value)
type Locals = [Value]

type Spine = [Value]
data Closure = Closure [Value] C.Term
  deriving Show

-- type annotation
type Type = Value

data Value
  = FunIntro Closure Type
  | FunType Type Closure
  | TypeType0
  | TypeType1
  | StuckFlexVar Type Global Spine
  | StuckRigidVar Type Level Spine
  | ElabError
  | ElabBlank

instance Show Value where
  show = \case
    FunIntro (Closure _ body) ty -> "v{" ++ show body ++ "}"
    FunType inTy (Closure env outTy) -> show inTy ++ " v-> " ++ show outTy ++ " " ++ show env
    TypeType0 -> "vU0"
    TypeType1 -> "vU0"
    StuckFlexVar _ gl spine -> "v~(?" ++ show (unGlobal gl) ++ " " ++ (concat $ intersperse " " (map show spine)) ++ ")"
    StuckRigidVar _ lv spine -> "v~(" ++ show (unLevel lv) ++ " " ++ (concat $ intersperse " " (map show spine)) ++ ")"
    ElabError -> "v<error>"
    ElabBlank -> "v<blank>"

type Norm a = Reader (Level, Metas, Locals) a

askLv :: Norm Level
askLv = do
  (lv, _, _) <- ask
  pure lv

askMetas :: Norm Metas
askMetas = do
  (_, metas, _) <- ask
  pure metas

askLocals :: Norm Locals
askLocals = do
  (_, _, locals) <- ask
  pure locals

appClosure :: HasCallStack => Closure -> Value -> Norm Value
appClosure (Closure locals body) val = do
  (level, metas, _) <- ask -- FIXME? store level with closure
  pure $ runReader (eval body) (level, metas, val:locals)

vApp :: HasCallStack => Value -> Value -> Norm Value
vApp lam arg = case lam of
  FunIntro body vty -> appClosure body arg
  StuckFlexVar vty gl spine -> pure $ StuckFlexVar vty gl (arg:spine)
  StuckRigidVar vty lv spine -> pure $ StuckRigidVar vty lv (arg:spine)
  _ -> error $ "Cannot `vApp` `" ++ show lam ++ "`"

vAppSpine :: HasCallStack => Value -> Spine -> Norm Value
vAppSpine val spine = case spine of
  arg:spine -> do
    lam <- vAppSpine val spine
    vApp lam arg
  [] -> pure val

vAppBis :: HasCallStack => Value -> Locals -> [C.BinderInfo] -> Norm Value
vAppBis val locals bis = do
  case (locals, bis) of
    (local:locals, C.Abstract:bis) -> do
      lam <- vAppBis val locals bis
      vApp lam local
    (_:locals, C.Concrete:bis) -> vAppBis val locals bis
    ([], []) -> pure val
    _ -> error ("impossible\n" ++ show locals ++ "\n" ++ show bis ++ "\n" ++ show val)

vMeta :: HasCallStack => Global -> Type -> Norm Value
vMeta gl vty = do
  metas <- askMetas
  pure $ case fromJust $ Map.lookup gl metas of
    Solved sol -> sol
    Unsolved -> StuckFlexVar vty gl []

bind :: HasCallStack => Value -> Norm a -> Norm a
bind ty act = do
  (level, metas, locals) <- ask
  pure $ runReader act (incLevel level, metas, (StuckRigidVar ty level []):locals)

define :: HasCallStack => Value -> Norm a -> Norm a
define val act = do
  (level, metas, locals) <- ask
  pure $ runReader act (incLevel level, metas, val:locals)

blank :: HasCallStack => Norm a -> Norm a
blank act = do
  (level, metas, locals) <- ask
  pure $ runReader act (incLevel level, metas, ElabBlank:locals)

-- withLocals :: HasCallStack => Norm a -> Locals -> Norm a
-- withLocals act locals = do
--   (level, metas, stages, _) <- ask
--   pure $ runReader act (level, metas, stages, locals)

index :: HasCallStack => Locals -> Index -> C.Type -> Int -> Value
index locals ix ty ix' = case locals of
  [] -> {-ElabError-} error $ "Nonexistent var `" ++ show ix ++ " :" ++ show ty ++ "`"
  x:xs ->
    if ix' == 0 then
      x
    else
      index xs ix ty (ix' - 1)

-- subst :: HasCallStack => C.Term -> Norm C.Term
-- subst trm = do
--   (_, _, locals) <- ask
--   case trm of
--     C.Var ix ty -> pure $ C.Value $ index locals ix ty (unIndex ix)
--     C.FunIntro body ty@(C.FunType inTy _) -> do
--       vInTy <- eval ty
--       C.FunIntro <$> bind vInTy (subst body) <*> subst ty
--     C.FunType inTy outTy -> do
--       vInTy <- eval inTy
--       C.FunType <$> subst inTy <*> bind vInTy (subst outTy)
--     C.FunElim lam arg -> C.FunElim <$> subst lam <*> subst arg
--     C.Let def defTy body -> do
--       vDefTy <- eval defTy
--       C.Let <$> subst def <*> subst defTy <*> bind vDefTy (subst body)
--     C.Meta gl tty -> C.Meta <$> pure gl <*> subst tty
--     C.InsertedMeta bis gl tty -> C.InsertedMeta <$> pure bis <*> pure gl <*> subst tty
--     _ -> pure trm

eval :: HasCallStack => C.Term -> Norm Value
eval trm = do
  (_, _, locals) <- ask
  case trm of
    C.Var ix ty -> pure $ let v = index locals ix ty (unIndex ix) in {-trace (("Var = "++) $ show v ++ show ix ++ show locals)-} v
    C.TypeType0 -> pure TypeType0
    C.TypeType1 -> pure TypeType1
    C.FunIntro body tty -> FunIntro (Closure locals body) <$> eval tty
    C.FunType inTy outTy -> do
      vInTy <- eval inTy
      pure $ FunType vInTy (Closure locals outTy)
    C.FunElim lam arg -> do
      vLam <- eval lam
      vArg <- eval arg
      vApp vLam vArg
    C.Let def _ body -> do
      vDef <- eval def
      define vDef $ eval body
    C.Meta gl tty -> vMeta gl =<< eval tty
    C.InsertedMeta bis gl tty -> (vMeta gl =<< eval tty) >>= \meta -> vAppBis meta locals bis
    C.ElabError -> pure ElabError

force :: HasCallStack => Value -> Norm Value
force val = do
  metas <- askMetas
  case val of
    StuckFlexVar vty gl spine | Solved sol <- fromJust $ Map.lookup gl metas -> do
      sol <- vAppSpine sol spine
      force sol
    _ -> pure val

lvToIx :: Level -> Level -> Index
lvToIx lv1 lv2 = Index (unLevel lv1 - unLevel lv2 - 1)

readbackSpine :: HasCallStack => C.Term -> Spine -> Norm C.Term
readbackSpine trm spine = do
  lv <- askLv
  case spine of
    arg:spine -> C.FunElim <$> readbackSpine trm spine <*> readback arg
    -- readbackSpine trm spine >>= \lam -> C.FunElim lam <$> readback lv arg
    [] -> pure trm

-- readbackTerm :: HasCallStack => C.Term -> Norm C.Term
-- readbackTerm trm = case trm of
--   C.FunIntro body ty@(C.FunType inTy _) -> C.FunIntro <$> blank (readbackTerm body) <*> readbackTerm ty
--   C.FunType inTy outTy -> C.FunType <$> readbackTerm inTy <*> blank (readbackTerm outTy)
--   C.FunElim lam arg -> C.FunElim <$> readbackTerm lam <*> readbackTerm arg
--   C.Let def defTy body -> C.Let <$> readbackTerm def <*> readbackTerm defTy <*> blank (readbackTerm body)
--   C.Meta gl ty -> C.Meta <$> pure gl <*> readbackTerm ty
--   C.InsertedMeta bis gl ty -> C.InsertedMeta <$> pure bis <*> pure gl <*> readbackTerm ty
--   C.Value val -> readback val
--   _ -> pure trm

-- TODO? replace `bind` with `blank`
readback :: HasCallStack => Value -> Norm C.Term
readback val = do
  val <- force val
  case val of
    StuckFlexVar vty gl spine -> do
      meta <- C.Meta <$> pure gl <*> readback vty
      readbackSpine meta spine
    StuckRigidVar vty lv' spine -> do
      lv <- askLv
      var <- C.Var <$> pure (lvToIx lv lv') <*> readback vty
      readbackSpine var spine
    FunIntro body vty@(FunType inTy _) -> do
      lv <- askLv
      vBody <- appClosure body (StuckRigidVar inTy lv [])
      C.FunIntro <$> blank (readback vBody) <*> readback vty
    FunType inTy outTy@(Closure env tmp) -> do
      -- let !() = trace ("      Env = " ++ show env) ()
      lv <- askLv
      vOutTy <- appClosure outTy (StuckRigidVar inTy lv []) 
      -- let !() = trace ("      outTy = " ++ show outTy) ()
      -- let !() = trace ("      vOutTy = " ++ show vOutTy) ()
      C.FunType <$> readback inTy <*> blank (readback vOutTy)
    TypeType0 -> pure C.TypeType0
    TypeType1 -> pure C.TypeType1
    ElabError -> pure C.ElabError
    _ -> pure C.ElabError