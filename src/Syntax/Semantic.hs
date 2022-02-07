module Syntax.Semantic where

import Syntax.Variable
import Syntax.Stage
import Syntax.Telescope qualified as T
import Syntax.Core qualified as C

data Declaration
  = Datatype Id Telescope
  | Constr Id Telescope Id [Term]
  | Term Term Term
  deriving (Eq)

data Term
  = FunType Term Closure
  | FunIntro Closure
  | DatatypeIntro Id [Term]
  | TypeType Stage
  | FreeVar Level
  | Let [Declaration] Closure
  -- Stuck terms
  | UniVar Global
  | StuckFunElim Term Term
  deriving (Eq)

viewApp :: Term -> (Term, [Term])
viewApp (StuckFunElim lam arg) =
  let (lam', args) = viewApp lam
  in (lam, args ++ [arg])
viewApp e = (e, [])

data Closure = Closure [Term] C.Term
  deriving (Eq)

type Telescope = T.Telescope Term