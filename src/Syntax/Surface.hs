module Syntax.Surface where

import Data.Text(Text)
import Numeric.Natural
import Syntax.Common hiding(unId, CStatement(..), Declaration(..))
import Text.Megaparsec(SourcePos)
import Data.Sequence

data Ast a where
  TermAst :: Term -> TermAst
  NameAst :: Name -> NameAst
  DeclAst :: Declaration -> Id -> DeclarationAst
  CStmtAst :: CStatement -> CStatementAst
  SourcePos :: Ast a -> SourcePos -> Ast a
deriving instance Show (Ast a)

unName :: NameAst -> Name
unName (NameAst name) = name

-- For declarations
data Universe = Obj | Meta | Prop
  deriving (Show)

unDeclName :: DeclarationAst -> Name
unDeclName (DeclAst (MetaTerm (NameAst name) _ _) _) = name
unDeclName (DeclAst (ObjTerm (NameAst name) _ _) _) = name
unDeclName (DeclAst (Axiom (NameAst name) _) _) = name
unDeclName (DeclAst (Prove _) did) = MachineName (fromIntegral did)
unDeclName (DeclAst (Fresh (NameAst name) _) _) = name
unDeclName (DeclAst (CFun (NameAst name) _ _ _) _) = name
unDeclName (SourcePos ast _) = unDeclName ast

unId :: DeclarationAst -> Id
unId (DeclAst _ did) = did
unId (SourcePos ast _) = unId ast

type NameAst = Ast Name

type SignatureAst = TermAst

type DeclarationAst = Ast Declaration
data Declaration
  = MetaTerm NameAst SignatureAst TermAst
  | ObjTerm NameAst SignatureAst TermAst
  | Axiom NameAst SignatureAst
  | Prove SignatureAst
  | Fresh NameAst SignatureAst
  | CFun NameAst (Seq (NameAst, TermAst)) TermAst CStatementAst
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
  | LiftCore TermAst
  | QuoteCore TermAst
  | SpliceCore TermAst
  | LiftLowCTm TermAst
  | QuoteLowCTm TermAst
  | SpliceLowCTm TermAst
   -- Carries return type
  | LiftLowCStmt TermAst
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
  | EqualProp TermAst TermAst
  | Bool
  | BTrue
  | BFalse
  -- case foo returns x. ty { true => body1, false => body2 }
  | Case TermAst (Maybe (NameAst, TermAst)) TermAst TermAst
  | Singleton TermAst
  | Sing
  | Equal TermAst TermAst
  | Refl
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
