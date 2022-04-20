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
  = MetaFunType ApplyMethod Term Closure
  | MetaFunIntro Closure
  | ObjFunType Term Closure
  | ObjFunIntro Closure
  | MetaConstIntro Id
  | ObjConstIntro Id
  | CodeCoreType Term
  | CodeCoreIntro Term
  | CodeLowCTmType Term
  | CodeLowCTmIntro Term
  | TypeType Stage
  | LocalVar Level
  | ElabError
  | Neutral (Maybe Term) Redex -- If `Nothing`, the term is stuck
  deriving (Eq, Show)

data Redex
  = MetaFunElim Term Term
  | ObjFunElim Term Term
  | CodeCoreElim Term
  | CodeLowCTmElim Term
  | GlobalVar Id
  | UniVar Global
  deriving (Eq, Show)

viewFunType :: Term -> Maybe (Term, Closure)
viewFunType (MetaFunType _ inTy outTy) = Just (inTy, outTy)
viewFunType (ObjFunType inTy outTy) = Just (inTy, outTy)
viewFunType _ = Nothing

pattern FunType inTy outTy <- (viewFunType -> Just (inTy, outTy))
