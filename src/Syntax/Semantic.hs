{-# LANGUAGE PatternSynonyms #-}
module Syntax.Semantic where

import Syntax.Extra
import Syntax.Core qualified as C
import Data.Map(Map)
import Data.Sequence
import Prelude hiding(length)

data Environment = Env (Seq Term) (Map Id Term)

withLocal :: Term -> Environment -> Environment
withLocal def (Env locals globals) = Env (def <| locals) globals

envSize :: Environment -> Int
envSize (Env locals _) = length locals

instance Show Environment where
  show (Env locals _) = show locals

data Closure = Clo Environment C.Term
  deriving (Show)

type Type = Term

data Term
  = MetaFunType ApplyMethod Term Closure
  | MetaFunIntro Closure
  | ObjectFunType Term Closure
  | ObjectFunIntro Closure
  | MetaConstantIntro Id
  | ObjectConstantIntro Id
  | CodeCoreType Term
  | CodeCoreIntro Term
  | CodeLowType Term
  | CodeLowIntro Term
  | TypeType Stage
  | LocalVar Level
  | ElabError
  | Neutral (Maybe Term) Redex -- If `Nothing`, the term is stuck
  deriving (Show)

data Redex
  = MetaFunElim Term Term
  | ObjectFunElim Term Term
  | CodeCoreElim Term
  | CodeLowElim Term
  | GlobalVar Id
  | UniVar Global
  deriving (Show)

viewFunType :: Term -> Maybe (Term, Closure)
viewFunType (MetaFunType _ inTy outTy) = Just (inTy, outTy)
viewFunType (ObjectFunType inTy outTy) = Just (inTy, outTy)
viewFunType _ = Nothing

pattern FunType inTy outTy <- (viewFunType -> Just (inTy, outTy))
