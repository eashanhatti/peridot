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
import {-# SOURCE #-} Normalization
import Control.Carrier.Reader
import Data.Functor.Identity
import Data.Text qualified as Text

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
  -- If `Nothing`, the term is stuck
  | Neutral (ReaderC NormContext Identity (Maybe Term)) Redex

instance Show Term where
  show (ObjFunType inTy outTy) = "(ObjFunType " ++ show inTy ++ " " ++ show outTy ++ ")"
  show (ObjFunIntro body) = "(ObjFunIntro " ++ show body ++ ")"
  show (MetaFunType inTy outTy) = "(MetaFunType " ++ show inTy ++ " " ++ show outTy ++ ")"
  show (MetaFunIntro body) = "(MetaFunIntro " ++ show body ++ ")"
  show (TypeType univ) = "(TypeType " ++ show univ ++ ")"
  show (LocalVar lvl) = "(LocalVar " ++ show lvl ++ ")"
  show (Rigid term) = "(Rigid " ++ show term ++ ")"
  show (Neutral _ redex) = "(Neutral _ (" ++ show redex ++ "))"

instance Eq Term where
  (==) = undefined -- FIXME

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
viewMetaFunElims (Neutral _ (MetaFunElim lam arg)) =
  let (lam', args) = viewMetaFunElims lam
  in (lam', args |> arg)
viewMetaFunElims term = (term, mempty)

pattern MetaFunElims lam args <- (viewMetaFunElims -> (lam, args))
