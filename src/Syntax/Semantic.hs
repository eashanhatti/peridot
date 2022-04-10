{-# LANGUAGE PatternSynonyms #-}
module Syntax.Semantic where

import Syntax.Extra
import Syntax.Core qualified as C
import Syntax.Quote qualified as Q
import Data.Map(Map, insert, size)

type TermQuote = Q.TermQuote Term

data Environment = Env [Term] (Map Id (Environment, C.Term))
  deriving (Eq)

instance Show Environment where
  show (Env locals _) = show locals

envSize (Env locals _) = length locals

withLocal :: Term -> Environment -> Environment
withLocal def (Env locals globals) = Env (def:locals) globals

withGlobal :: Id -> Environment -> C.Term -> Environment -> Environment
withGlobal did env term (Env locals globals) = Env locals (insert did (env, term) globals)

type Type = Term

data Term
  = MetaFunType ApplyMethod Term Closure
  | MetaFunIntro Closure
  | ObjectFunType Term Closure
  | ObjectFunIntro Closure
  | MetaConstantIntro Id
  | ObjectConstantIntro Id
  | IOType Term
  | IOIntroPure Term -- `pure`
  | IOIntroBind IOOperation Term -- `>>=`
  | UnitType
  | UnitIntro
  | QuoteIntro TermQuote
  | QuoteType TermQuote
  | TypeType Stage
  | EElabError
  -- Stuck terms
  | UniVar Global
  | FreeVar Level
  | TopVar Id Environment C.Term
  | ObjectFunElim Term Term
  | MetaFunElim Term Term
  deriving (Eq, Show)

viewFunType :: Term -> Maybe (Term, Closure)
viewFunType (MetaFunType _ inTy outTy) = Just (inTy, outTy)
viewFunType (ObjectFunType inTy outTy) = Just (inTy, outTy)
viewFunType _ = Nothing

pattern FunType inTy outTy <- (viewFunType -> Just (inTy, outTy))

viewApp :: Term -> (Term, [Term])
viewApp (MetaFunElim lam arg) =
  let (lam', args) = viewApp lam
  in (lam, args ++ [arg])
viewApp (ObjectFunElim lam arg) =
  let (lam', args) = viewApp lam
  in (lam, args ++ [arg])
viewApp e = (e, [])

viewMC :: Term -> Maybe (Id, [Term])
viewMC (viewApp -> (MetaConstantIntro did, args)) = Just (did, args)
viewMC _ = Nothing

data Closure = Closure Environment C.Term
  deriving (Eq, Show)
