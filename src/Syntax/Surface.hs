module Syntax.Surface where

import Data.Text(Text)
import Numeric.Natural
import Syntax.Variable
import Syntax.Telescope

data Ast a where
  TermAst :: Term -> TermAst
  NameAst :: Name -> NameAst
  DeclAst :: Declaration -> Id -> DeclarationAst
  ConstrAst :: Constructor -> Id -> ConstructorAst
  TeleAst :: Telescope (Name, TermAst) -> TelescopeAst

unName :: NameAst -> Name
unName (NameAst name) = name

unDeclName :: DeclarationAst -> Name
unDeclName (DeclAst (Datatype (unName -> name) _ _) _) = name
unDeclName (DeclAst (Term (unName -> name) _ _) _) = name

unId :: DeclarationAst -> Id
unId (DeclAst _ did) = did

type NameAst = Ast Name

type TelescopeAst = Ast (Telescope (Name, TermAst))

type DeclarationAst = Ast Declaration
data Declaration
  = Datatype NameAst TelescopeAst [ConstructorAst]
  | Term NameAst TermAst TermAst

type ConstructorAst = Ast Constructor
data Constructor = Constructor NameAst TelescopeAst [TermAst]

type TermAst = Ast Term
data Term
  = Pi TelescopeAst TermAst
  | Lam [NameAst] TermAst
  | App TermAst [TermAst]
  | Var Name
  | Univ
  | Let [DeclarationAst] TermAst