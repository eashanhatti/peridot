module Elaboration.Decl where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Common
import Elaboration.Effect
import Control.Effect.Reader
import Data.Map qualified as Map
import {-# SOURCE #-} Elaboration.Term qualified as EE
import Elaboration.CStatement qualified as ES
import Normalization hiding(eval)
import Control.Monad
import Control.Monad.Extra
import Data.Foldable(toList, foldl')
import Data.Traversable
import GHC.Stack
import Data.Sequence
import Prelude hiding(traverse, map, zip)

check :: HasCallStack => Elab sig m => Id -> m C.Declaration
check did = memo (CheckDecl did) $ withDecl did $ withPos' $ \decl -> do
  (cSig, univ) <- declType (unPDDeclId decl)
  case decl of
    PDDecl (DeclAst (ObjTerm name _ def) did) -> do
      cDef <- eval cSig >>= EE.check def
      unify univ (N.TypeType N.Obj)
      pure (C.ObjTerm did cSig cDef)
    PDDecl (DeclAst (MetaTerm name _ def) did) -> do
      cDef <- eval cSig >>= EE.check def
      unify univ (N.TypeType N.Meta)
      pure (C.MetaTerm did cSig cDef)
    PDDecl (DeclAst (Datatype name _ _) did) -> do
      vSig <- eval cSig
      unify vSig (N.TypeType N.Obj)
      pure (C.ObjConst did cSig)
    PDDecl (DeclAst (Axiom name _) did) ->
      pure (C.MetaConst did cSig)
    PDDecl (DeclAst (Prove _) did) ->
      pure (C.Prove did cSig)
    PDDecl (DeclAst (Fresh name _) did) ->
      pure (C.Fresh did cSig)
    PDConstr constr@(ConstrAst (Constr _ _) did dtDid) -> do
      unify univ (N.TypeType N.Obj)
      pure (C.ObjConst did cSig)
    PDDecl (DeclAst (CFun _ (fmap (unName . fst) -> names) _ stmt) did) ->
      case cSig of
        C.Rigid (C.CFunType inTys outTy) -> do
          vInTys <- traverse eval inTys
          (cStmt, retTy) <- bindLocalMany (zip names vInTys) (ES.infer stmt)
          vOutTy <- eval outTy
          unify vOutTy retTy
          pure (C.CFun did inTys outTy cStmt)

withPos' :: HasCallStack => Elab sig m => (Predeclaration -> m a) -> (Predeclaration -> m a)
withPos' act (PDDecl (SourcePos ast pos)) = withPos pos (act (PDDecl ast))
withPos' act (PDConstr (SourcePos ast pos)) = withPos pos (act (PDConstr ast))
withPos' act pd = act pd

declType :: HasCallStack => Query sig m => Id -> m (C.Term, N.Term)
declType did = memo (DeclType did) $ withDecl did $ withPos' $ \decl ->
  case decl of
    PDDecl (DeclAst (ObjTerm name sig def) _) -> EE.checkObjType sig
    PDDecl (DeclAst (MetaTerm name sig def) _) -> EE.checkMetaType sig
    PDDecl (DeclAst (Datatype name sig _) _) -> EE.checkObjType sig
    PDDecl (DeclAst (Axiom name sig) _) -> EE.checkMetaType sig
    PDDecl (DeclAst (Prove sig) _) -> EE.checkMetaType sig
    PDDecl (DeclAst (Fresh name sig) _) -> EE.checkMetaType sig
    PDDecl (DeclAst (CFun _ (fmap snd -> inTys) outTy _) _) -> do
      cInTys <- traverse (flip EE.check (N.TypeType (N.Low C))) inTys
      cOutTy <- EE.check outTy (N.TypeType (N.Low C))
      pure (C.Rigid (C.CFunType cInTys cOutTy), N.TypeType (N.Low C))
    PDConstr constr@(ConstrAst (Constr _ sig) _ _) -> EE.checkObjType sig -- TODO: Form check
