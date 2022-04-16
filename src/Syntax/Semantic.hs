{-# LANGUAGE PatternSynonyms #-}
module Syntax.Semantic where

import Syntax.Extra
import Syntax.Core qualified as C
import Data.Map(Map)
import Data.Sequence
import Prelude hiding(length)

data Environment = Env (Seq Term) (Map Id Term)

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
  | ElabError
  | Neutral Term Redex
  deriving (Show)

data Redex
  = MetaFunElim Term Term
  | ObjectFunElim Term Term
  | CodeCoreElim Term
  | CodeLowElim Term
  | LocalVar Level
  | GlobalVar Id
  | UniVar Global
  deriving (Show)

viewFunType :: Term -> Maybe (Term, Closure)
viewFunType (MetaFunType _ inTy outTy) = Just (inTy, outTy)
viewFunType (ObjectFunType inTy outTy) = Just (inTy, outTy)
viewFunType _ = Nothing

pattern FunType inTy outTy <- (viewFunType -> Just (inTy, outTy))
