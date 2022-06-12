module Syntax.Surface where

import Data.Text(Text)
import Numeric.Natural
import Syntax.Common hiding(unId, CStatement(..), Declaration(..))
import Syntax.Common qualified as Cm
import Text.Megaparsec(SourcePos)
import Data.Sequence

data Ast a where
  TermAst :: Term -> TermAst
  NameAst :: Name -> NameAst
  DeclAst :: Declaration -> Id -> DeclarationAst
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
unDeclName (SourcePos ast _) = unDeclName ast

stripSourcePos :: DeclarationAst -> Declaration
stripSourcePos (SourcePos ast _) = stripSourcePos ast
stripSourcePos (DeclAst decl _) = decl

unId :: DeclarationAst -> Id
unId (DeclAst _ did) = did
unId (SourcePos ast _) = unId ast

type NameAst = Ast Name

type DeclarationAst = Ast Declaration
data Declaration
  = MetaTerm NameAst TermAst TermAst
  | ObjTerm NameAst TermAst TermAst
  | CTerm NameAst TermAst TermAst
  | Axiom NameAst TermAst
  | Prove TermAst
  | Fresh NameAst TermAst
  deriving (Show)

type TermAst = Ast Term
data Term
  = MetaPi PassMethod NameAst TermAst TermAst
  | MetaLam (Seq NameAst) TermAst
  | ObjPi PassMethod NameAst TermAst TermAst
  | ObjLam (Seq (PassMethod, NameAst)) TermAst
  | App TermAst (Seq (PassMethod, TermAst))
  | Var Name
  | OUniv
  | MUniv
  | LCUniv
  | Let (Seq DeclarationAst) TermAst
  | LiftObj TermAst
  | QuoteObj TermAst
  | SpliceObj TermAst
  | LiftC TermAst
  | QuoteC TermAst
  | SpliceC TermAst
  | ImplProp TermAst TermAst
  | ConjProp TermAst TermAst
  | DisjProp TermAst TermAst
  | ForallProp TermAst
  | ExistsProp TermAst
  | EqualProp TermAst TermAst
  | Bool
  | BTrue
  | BFalse
  | Case TermAst TermAst TermAst
  | Equal TermAst TermAst
  | Refl
  | Sig (Seq (NameAst, TermAst))
  | Struct (Seq (NameAst, TermAst))
  | Select TermAst NameAst
  | Patch TermAst (Seq (NameAst, TermAst))
  | ListTypeNil
  | ListTypeCons TermAst TermAst
  | ListNil
  | ListCons TermAst TermAst
  | CIntType
  | CInt Int
  | CPtrType TermAst
  | CLValType TermAst
  | CStmtType
  | CReturn
  | CIf TermAst TermAst TermAst
  | CWhile TermAst TermAst
  | CBreak
  | CStructType TermAst
  | CStruct TermAst
  | CApp TermAst TermAst
  | CAdd TermAst TermAst
  | CSeq TermAst TermAst
  | CDeclVar TermAst TermAst
  | CAssign TermAst TermAst
  | CEq TermAst TermAst
  | CRef TermAst
  | CDerefLVal TermAst -- deref pointer into lval
  | CDerefRVal TermAst -- deref pointer into rval
  | CCast TermAst TermAst
  | CLam TermAst
  | CLamType TermAst
  | Declare TermAst TermAst TermAst
  | Define TermAst TermAst TermAst
  | CDeclare TermAst TermAst TermAst
  | CDefine TermAst TermAst TermAst
  | NameType Cm.Universe TermAst
  deriving (Show)
