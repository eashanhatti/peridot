module Syntax.Surface where

import Data.Text(Text)
import Numeric.Natural
import Syntax.Extra

data Ast a where
  TermAst :: Term -> TermAst
  NameAst :: Name -> NameAst
  DeclAst :: Declaration -> Id -> DeclarationAst
  -- .., constr id, datatype id
  ConstrAst :: Constructor -> Id -> Id -> ConstructorAst
deriving instance Show (Ast a)

unName :: NameAst -> Name
unName (NameAst name) = name

unDeclName :: DeclarationAst -> Name
unDeclName (DeclAst (Datatype (NameAst name) _ _) _) = name
unDeclName (DeclAst (Term (NameAst name) _ _) _) = name
unDeclName (DeclAst (Axiom (NameAst name) _) _) = name
unDeclName (DeclAst (Prove _) did) = MachineName (fromIntegral did)
unDeclName (DeclAst (Fresh (NameAst name) _) _) = name

unConstrName :: ConstructorAst -> Name
unConstrName (ConstrAst (Constr (NameAst name) _) _ _) = name

unId :: DeclarationAst -> Id
unId (DeclAst _ did) = did

unCId :: ConstructorAst -> Id
unCId (ConstrAst _ did _) = did

type NameAst = Ast Name

type SignatureAst = TermAst

type DeclarationAst = Ast Declaration
data Declaration
  = Datatype NameAst SignatureAst [ConstructorAst]
  | Term NameAst SignatureAst TermAst
  | Axiom NameAst SignatureAst
  | Prove SignatureAst
  | Fresh NameAst SignatureAst
  deriving (Show)

type ConstructorAst = Ast Constructor
data Constructor = Constr NameAst SignatureAst
  deriving (Show)

type TermAst = Ast Term
data Term
  = Pi NameAst TermAst TermAst
  | Lam [NameAst] TermAst
  | App TermAst [TermAst]
  | Var Name
  | Univ
  | Let [DeclarationAst] TermAst
  | Rule TermAst TermAst -- Foo :- Bar, or Foo <- Bar, or Bar -> Foo
  | IOPure TermAst
  | IOType TermAst
  | IOBind IOOperation TermAst
  | UnitType
  | Unit
  deriving (Show)
