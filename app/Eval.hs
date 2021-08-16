{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}

module Eval where

import Var
import qualified Core as C
import qualified Data.Map as Map
import Data.Maybe(fromJust)

data MetaEntry = Solved Value | Unsolved
  deriving Show

type Metas = Map.Map Global MetaEntry
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
  | TypeType
  deriving Show

data Neutral
  = FlexVar Type Global Spine
  | RigidVar Type Level Spine
  deriving Show

pattern StuckFlexVar ty gl spine = Stuck (FlexVar ty gl spine)
pattern StuckRigidVar ty lv spine = Stuck (RigidVar ty lv spine)

appClosure :: Metas -> Closure -> Value -> Value
appClosure metas (Closure locals body) val = eval metas (val:locals) body

vApp :: Metas -> Value -> Value -> Value
vApp metas lam arg = case lam of
  FunIntro body vty -> appClosure metas body arg
  StuckFlexVar vty gl spine -> StuckFlexVar vty gl (arg:spine)
  StuckRigidVar vty lv spine -> StuckRigidVar vty lv (arg:spine)

vAppSpine :: Metas -> Value -> Spine -> Value
vAppSpine metas val spine = case spine of
  arg:spine -> vApp metas (vAppSpine metas val spine) arg
  [] -> val

vAppBis :: Metas -> Locals -> Value -> [C.BinderInfo] -> Value
vAppBis metas locals val bis = case (locals, bis) of
  (local:locals, C.Abstract:bis) -> vApp metas (vAppBis metas locals val bis) local
  (_:locals, C.Concrete:bis) -> vAppBis metas locals val bis
  ([], []) -> val

vMeta :: Metas -> Global -> Type -> Value
vMeta metas gl vty = case fromJust $ Map.lookup gl metas of
  Solved sol -> sol
  Unsolved -> StuckFlexVar vty gl []

eval :: Metas -> Locals -> C.Term -> Value
eval metas locals trm = case trm of
  C.Var ix _ -> locals !! unIndex ix
  C.TypeType -> TypeType
  C.FunIntro body tty -> FunIntro (Closure locals body) (eval metas locals tty)
  C.FunType inTy outTy -> FunType (eval metas locals inTy) (Closure locals outTy)
  C.FunElim lam arg -> vApp metas (eval metas locals lam) (eval metas locals arg)
  C.Let def body -> eval metas ((eval metas locals def):locals) body
  C.Meta gl tty -> vMeta metas gl (eval metas locals tty)
  C.InsertedMeta bis gl tty -> vAppBis metas locals (vMeta metas gl (eval metas locals tty)) bis

force :: Metas -> Value -> Value
force metas val = case val of
  StuckFlexVar vty gl spine | Solved sol <- fromJust $ Map.lookup gl metas -> force metas (vAppSpine metas sol spine)
  _ -> val

lvToIx :: Level -> Level -> Index
lvToIx lv1 lv2 = Index (unLevel lv1 - unLevel lv2 - 1)

readbackSpine :: Metas -> Level -> C.Term -> Spine -> C.Term
readbackSpine metas lv trm spine = case spine of
  arg:spine -> C.FunElim (readbackSpine metas lv trm spine) (readback metas lv arg)
  [] -> trm

readback :: Metas -> Level -> Value -> C.Term
readback metas lv val = case force metas val of
  StuckFlexVar vty gl spine -> readbackSpine metas lv (C.Meta gl (readback metas lv vty)) spine
  StuckRigidVar vty lv' spine -> readbackSpine metas lv (C.Var (lvToIx lv lv') (readback metas lv vty)) spine
  FunIntro body vty@(FunType inTy _) -> C.FunIntro (readback metas (Level $ unLevel lv + 1) (appClosure metas body (StuckRigidVar inTy lv []))) (readback metas lv vty)
  FunType inTy outTy -> C.FunType (readback metas lv inTy) (readback metas (Level $ unLevel lv + 1) (appClosure metas outTy (StuckRigidVar inTy lv [])))
  TypeType -> C.TypeType