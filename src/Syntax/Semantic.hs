module Syntax.Semantic where

import Syntax.Extra
import Syntax.Core qualified as C
import Data.Map(Map, insert, size)

data Environment = Env [Term] (Map Id (Environment, C.Term))
  deriving (Eq)

envSize (Env locals _) = length locals

withLocal :: Term -> Environment -> Environment
withLocal def (Env locals globals) = Env (def:locals) globals

withGlobal :: Id -> Environment -> C.Term -> Environment -> Environment
withGlobal did env term (Env locals globals) = Env locals (insert did (env, term) globals)

data Term
  = FunType ApplyMethod Term Closure
  | FunIntro Closure
  | MetaConstantIntro Id
  | ObjectConstantIntro Id
  | TypeType Stage
  | EElabError
  -- Stuck terms
  | UniVar Global
  | FreeVar Level
  | TopVar Id Environment C.Term
  | FunElim Term Term
  deriving (Eq)

viewApp :: Term -> (Term, [Term])
viewApp (FunElim lam arg) =
  let (lam', args) = viewApp lam
  in (lam, args ++ [arg])
viewApp e = (e, [])

data Closure = Closure Environment C.Term
  deriving (Eq)