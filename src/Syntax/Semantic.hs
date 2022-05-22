{-# LANGUAGE PatternSynonyms #-}
module Syntax.Semantic
( module Syntax.Semantic
, module Syntax.Common
) where

import Syntax.Common hiding(Declaration)
import Syntax.Common qualified as Cm
import Syntax.Core qualified as C
import Data.Map(Map, insert)
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

withGlobal :: Id -> Term -> Environment -> Environment
withGlobal did def (Env locals globals) = Env locals (insert did def globals)

envSize :: Environment -> Int
envSize (Env locals _) = length locals

instance Show Environment where
  show (Env locals _) = show locals

data Closure = Clo Environment C.Term
  deriving (Eq, Show)

type Declaration = Cm.Declaration Term

type Type = Term

data Term
  -- Object level
  = ObjFunType Term Closure
  | ObjFunIntro Closure
  | RecType (Seq (Field, Closure))
  | RecIntro (Seq (Field, Term))
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
  show (RecType tys) = "(RecType " ++ show tys ++ ")"
  show (RecIntro tys) = "(RecIntro " ++ show tys ++ ")"
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
  | TwoElim Term Closure Term Term
  | RecElim Term Field
  | SingElim Term
  | Let (Seq Declaration) Term
  deriving (Eq, Show)

data Universe = Meta | Obj | Low Language | SUniVar Global
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
