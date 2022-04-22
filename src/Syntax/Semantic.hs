{-# LANGUAGE PatternSynonyms #-}
module Syntax.Semantic where

import Syntax.Common
import Syntax.Core qualified as C
import Data.Map(Map)
import Data.Sequence
import Prelude hiding(length)

data Environment = Env
  { unLocals :: Seq Term
  , unGlobals :: Map Id Term }
  deriving (Eq)

withLocal :: Term -> Environment -> Environment
withLocal def (Env locals globals) = Env (def <| locals) globals

envSize :: Environment -> Int
envSize (Env locals _) = length locals

instance Show Environment where
  show (Env locals _) = show locals

data Closure = Clo Environment C.Term
  deriving (Eq, Show)

type Type = Term

data Term
  -- Object level
  = ObjFunType Term Closure
  | ObjFunIntro Closure
  | ObjConstIntro Id
  -- Low C level
  | CIntIntro Int
  | COp (COp Term)
  | CFunCall Term (Seq Term)
  -- Meta level
  | MetaFunType ApplyMethod Term Closure
  | MetaFunIntro Closure
  | MetaConstIntro Id
  | CodeCoreType Term
  | CodeCoreIntro Term
  | CodeLowCTmType Term
  | CodeLowCTmIntro Term
  | CodeLowCStmtType Term -- Carries return type
  | CodeLowCStmtIntro (CStatement Term)
  | CPtrType Term
  | CIntType
  | CVoidType
  | CValType ValueCategory Term
  | CFunType (Seq Term) Term
  -- Other
  | TypeType Stage
  | LocalVar Level
  | ElabError
  | Neutral (Maybe Term) Redex -- If `Nothing`, the term is stuck
  deriving (Eq, Show)

pattern CRValType ty = CValType RVal ty
pattern CLValType ty = CValType LVal ty

data Redex
  = MetaFunElim Term Term
  | ObjFunElim Term Term
  | CodeCoreElim Term
  | CodeLowCTmElim Term
  | GlobalVar Id
  | UniVar Global
  deriving (Eq, Show)

data Stage = Meta | Obj | Low Language | SUniVar Global
  deriving (Eq, Show)

data ValueCategory = LVal | RVal | VCUniVar Global
  deriving (Eq, Show)

viewFunType :: Term -> Maybe (Term, Closure)
viewFunType (MetaFunType _ inTy outTy) = Just (inTy, outTy)
viewFunType (ObjFunType inTy outTy) = Just (inTy, outTy)
viewFunType _ = Nothing

pattern FunType inTy outTy <- (viewFunType -> Just (inTy, outTy))
