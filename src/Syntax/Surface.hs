module Syntax.Surface where

import Data.Text(Text)
import Numeric.Natural
import Syntax.Variable
import Syntax.Telescope

data Ast a where
  TermAst :: Term -> TermAst
  NameAst :: Name -> NameAst
  DeclAst :: Declaration -> Id -> DeclarationAst
  -- .., constr id, datatype id
  ConstrAst :: Constructor -> Id -> Id -> ConstructorAst
  TeleAst :: Telescope (Name, TermAst) -> TelescopeAst

unName :: NameAst -> Name
unName (NameAst name) = name

unDeclName :: DeclarationAst -> Name
unDeclName (DeclAst (Datatype (NameAst name) _ _) _) = name
unDeclName (DeclAst (Term (NameAst name) _ _) _) = name

unConstrName :: ConstructorAst -> Name
unConstrName (ConstrAst (Constr (NameAst name) _ _) _ _) = name

unId :: DeclarationAst -> Id
unId (DeclAst _ did) = did

unCId :: ConstructorAst -> Id
unCId (ConstrAst _ did _) = did

type NameAst = Ast Name

type TelescopeAst = Ast (Telescope (Name, TermAst))

type DeclarationAst = Ast Declaration
data Declaration
  = Datatype NameAst TelescopeAst [ConstructorAst]
  | Term NameAst TermAst TermAst

type ConstructorAst = Ast Constructor
data Constructor = Constr NameAst TelescopeAst [TermAst]

type TermAst = Ast Term
data Term
  = Pi NameAst TermAst TermAst
  | Lam [NameAst] TermAst
  | App TermAst [TermAst]
  | Var Name
  | Univ
  | Let [DeclarationAst] TermAst