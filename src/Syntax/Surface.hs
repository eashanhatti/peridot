module Syntax.Surface where

import Data.Text(Text)
import Numeric.Natural
import Syntax.Common hiding(unId, CStatement(..))
import Text.Megaparsec(SourcePos)
import Data.Sequence

data Ast a where
  TermAst :: Term -> TermAst
  NameAst :: Name -> NameAst
  DeclAst :: Declaration -> Id -> DeclarationAst
  -- .., constr id, datatype id
  ConstrAst :: Constructor -> Id -> Id -> ConstructorAst
  CStmtAst :: CStatement -> CStatementAst
  SourcePos :: Ast a -> SourcePos -> Ast a
deriving instance Show (Ast a)

unName :: NameAst -> Name
unName (NameAst name) = name

viewConstrs :: DeclarationAst -> Maybe (Seq ConstructorAst)
viewConstrs (SourcePos ast _) = viewConstrs ast
viewConstrs (DeclAst (Datatype _ _ cs) _) = Just cs
viewConstrs _ = Nothing

unDeclName :: DeclarationAst -> Name
unDeclName (DeclAst (Datatype (NameAst name) _ _) _) = name
unDeclName (DeclAst (MetaTerm (NameAst name) _ _) _) = name
unDeclName (DeclAst (ObjTerm (NameAst name) _ _) _) = name
unDeclName (DeclAst (Axiom (NameAst name) _) _) = name
unDeclName (DeclAst (Prove _) did) = MachineName (fromIntegral did)
unDeclName (DeclAst (Fresh (NameAst name) _) _) = name
unDeclName (DeclAst (CFun (NameAst name) _ _ _) _) = name
unDeclName (SourcePos ast _) = unDeclName ast

unConstrName :: ConstructorAst -> Name
unConstrName (ConstrAst (Constr (NameAst name) _) _ _) = name
unConstrName (SourcePos ast _) = unConstrName ast

unId :: DeclarationAst -> Id
unId (DeclAst _ did) = did
unId (SourcePos ast _) = unId ast

unCId :: ConstructorAst -> Id
unCId (ConstrAst _ did _) = did
unCId (SourcePos ast _) = unCId ast

type NameAst = Ast Name

type SignatureAst = TermAst

type DeclarationAst = Ast Declaration
data Declaration
  = Datatype NameAst SignatureAst (Seq ConstructorAst)
  | MetaTerm NameAst SignatureAst TermAst
  | ObjTerm NameAst SignatureAst TermAst
  | Axiom NameAst SignatureAst
  | Relation NameAst SignatureAst NameAst SignatureAst
  | Prove SignatureAst
  | Fresh NameAst SignatureAst
  | CFun NameAst (Seq (NameAst, TermAst)) TermAst CStatementAst
  deriving (Show)

type ConstructorAst = Ast Constructor
data Constructor = Constr NameAst SignatureAst
  deriving (Show)

type TermAst = Ast Term
data Term
  = MetaPi NameAst TermAst TermAst
  | MetaLam (Seq NameAst) TermAst
  | ObjPi NameAst TermAst TermAst
  | ObjLam (Seq NameAst) TermAst
  | App TermAst (Seq TermAst)
  | Var Name
  | OUniv
  | MUniv
  | LCUniv
  | Let (Seq DeclarationAst) TermAst
  | Rule TermAst TermAst -- Foo :- Bar, or Foo <- Bar, or Bar -> Foo
  | LiftCore TermAst
  | QuoteCore TermAst
  | SpliceCore TermAst
  | LiftLowCTm TermAst
  | QuoteLowCTm TermAst
  | SpliceLowCTm TermAst
  | LiftLowCStmt TermAst -- Carries return type
  | QuoteLowCStmt CStatementAst
  | CIntType
  | CVoidType
  | CPtrType TermAst
  -- | CLValType TermAst
  -- | CRValType TermAst
  | CRef TermAst
  | CDeref TermAst
  | CAdd TermAst TermAst
  | CSub TermAst TermAst
  | CLess TermAst TermAst
  | CGrtr TermAst TermAst
  | CEql TermAst TermAst
  | CFunCall TermAst (Seq TermAst)
  | CFunType (Seq TermAst) TermAst
  | CInt Int
  | ImplProp TermAst TermAst
  | ConjProp TermAst TermAst
  | DisjProp TermAst TermAst
  | ForallProp TermAst
  | ExistsProp TermAst
  deriving (Show)

type CStatementAst = Ast CStatement
data CStatement
  = Block (Seq CStatementAst)
  | If TermAst CStatementAst CStatementAst
  | VarDecl NameAst TermAst
  | Assign TermAst TermAst
  | Return (Maybe TermAst)
  | SpliceLowCStmt TermAst
  deriving (Show)
