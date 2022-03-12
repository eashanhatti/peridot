module Elaboration.Decl where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Extra
import Elaboration.Effect
import Control.Effect.Reader
import Data.Map qualified as Map
import {-# SOURCE #-} Elaboration.Term qualified as EE
import Normalization
import Control.Monad
import Control.Monad.Extra
import Data.Foldable(toList, foldl')

check :: Elab sig m => Id -> m C.Declaration
check did = memo (CheckDecl did) $ withDecl did $ withPos' $ \decl -> do
  cSig <- declType (unPDDeclId decl)
  case decl of
    PDDecl (DeclAst (Term name _ def) did) -> do
      cDef <- eval cSig >>= EE.check def
      pure (C.Term did cSig cDef)
    PDDecl (DeclAst (Datatype name _ _) did) ->
      pure (C.ObjectConstant did cSig)
    PDDecl (DeclAst (Axiom name _) did) ->
      pure (C.MetaConstant did cSig)
    PDDecl (DeclAst (Prove _) did) ->
      pure (C.Prove did cSig)
    PDDecl (DeclAst (Fresh name _) did) ->
      pure (C.Fresh did cSig)
    PDConstr constr@(ConstrAst (Constr _ _) did dtDid) ->
      pure (C.ObjectConstant did cSig)

withPos' :: Elab sig m => (Predeclaration -> m a) -> (Predeclaration -> m a)
withPos' act (PDDecl (SourcePos ast pos)) = withPos pos (act (PDDecl ast))
withPos' act (PDConstr (SourcePos ast pos)) = withPos pos (act (PDConstr ast))
withPos' act pd = act pd

declType :: Query sig m => Id -> m C.Term
declType did = memo (DeclType did) $ withDecl did $ withPos' $ \decl ->
  case decl of
    PDDecl (DeclAst (Term name sig def) did) -> EE.checkObjectType sig
    PDDecl (DeclAst (Datatype name sig _) did) -> EE.checkObjectType sig
    PDDecl (DeclAst (Axiom name sig) did) -> EE.checkMetaType sig
    PDDecl (DeclAst (Prove sig) did) -> EE.checkMetaType sig
    PDDecl (DeclAst (Fresh name sig) did) -> EE.checkMetaType sig
    PDConstr constr@(ConstrAst (Constr _ sig) did dtDid) -> EE.checkObjectType sig -- TODO: Form check
