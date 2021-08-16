module Elaboration where

import Data.Map(Map)
import qualified Eval as E
import qualified Unification as U
import qualified Surface as S
import qualified Core as C
import Var

data Name = Name String 

data Error = UnboundName Name | UnifyError U.Error

data ElabState = Context
  { locals :: E.Locals
  , metas :: E.Metas
  , lv :: Level
  , errs :: [Error]
  , spn :: S.Span
  , bis :: [C.BinderInfo]
  , probs :: U.PendingProblems
  , goal :: C.Term
  , term :: C.Term }

type Elab = State ElabState

elabTerm :: S.Term -> Elab C.Term
elabTerm trm = do