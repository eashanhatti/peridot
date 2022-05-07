{-# LANGUAGE PatternSynonyms #-}
module Syntax.Semantic
( module Syntax.Semantic
, module Syntax.Common
) where

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
  -- Meta level
  | MetaFunType Term Closure
  | MetaFunIntro Closure
  -- Other
  | TypeType Universe
  | LocalVar Level
  | Rigid (RigidTerm Term)
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

data Universe = Meta | Obj | Low Language | Prop | SUniVar Global
  deriving (Eq, Show)

viewFunType :: Term -> Maybe (Term, Closure)
viewFunType (MetaFunType inTy outTy) = Just (inTy, outTy)
viewFunType (ObjFunType inTy outTy) = Just (inTy, outTy)
viewFunType _ = Nothing

pattern FunType inTy outTy <- (viewFunType -> Just (inTy, outTy))

viewMetaFunElims :: Term -> (Term, Seq Term)
viewMetaFunElims (Neutral (Just term) _) = viewMetaFunElims term
viewMetaFunElims (Neutral Nothing (MetaFunElim lam arg)) =
  let (lam', args) = viewMetaFunElims lam
  in (lam', args |> arg)
viewMetaFunElims term = (term, mempty)

pattern MetaFunElims lam args <- (viewMetaFunElims -> (lam, args))
