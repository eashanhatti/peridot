module Syntax.Surface where

import Data.Text(Text)
import Numeric.Natural

data Ast a where
  TermAst :: Term -> TermAst
  NameAst :: Name -> NameAst
  DeclarationAst :: Declaration -> DeclarationAst

type NameAst = Ast Name
data NameAst = UserName Text | MachineName Natural

type TelescopeAst = Ast Telescope
data Telescope
  = Empty
  | Bind NameAst TermAst TelescopeAst

type DeclarationAst = Ast Declaration
data Declaration
  = Datatype TelescopeAst [Constructor]
  | Definition TermAst TermAst

type ConstructorAst = Ast Constructor
data Constructor = Constructor NameAst TelescopeAst NameAst [TermAst]

type TermAst = Ast Term
data Term
  = Pi TelescopeAst TermAst
  | Lam [NameAst] TermAst
  | App TermAst [TermAst]
  | Var NameAst
  | Univ
  | Let [DeclarationAst] TermAst