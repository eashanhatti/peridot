module Elaboration.Declaration where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Common hiding(Declaration(..))
import Elaboration.Effect
import Control.Effect.Reader
import Control.Effect.State
import Control.Carrier.NonDet.Church hiding(Empty)
import Data.Map qualified as Map
import Data.Set qualified as Set
import {-# SOURCE #-} Elaboration.Term qualified as EE
import Elaboration.CStatement qualified as ES
import Normalization hiding(eval)
import Control.Monad
import Control.Monad.Extra
import Data.Foldable(toList, foldl')
import Data.Traversable
import GHC.Stack
import Data.Sequence
import Search
import Prelude hiding(traverse, map, zip, concat, filter, mapWithIndex)
import Debug.Trace
import Extra

constDecl :: Universe -> (Id -> C.Term -> C.Declaration)
constDecl Obj = C.ObjConst
constDecl Meta = C.MetaConst

check :: HasCallStack => Elab sig m => Id -> m C.Declaration
check did = memo (CheckDecl did) $ withDecl did $ withPos' $ \decl -> do
  (cSig, univ) <- declType (unPDDeclId decl)
  case decl of
    PDDecl (DeclAst (ObjTerm name _ def) did) -> do
      cDef <- eval cSig >>= EE.check def
      pure (C.ObjTerm did cSig cDef)
    PDDecl (DeclAst (MetaTerm name _ def) did) -> do
      cDef <- eval cSig >>= EE.check def
      pure (C.MetaTerm did cSig cDef)
    PDDecl (DeclAst (Datatype name _ _) did) ->
      pure (C.ObjConst did cSig)
    PDDecl (DeclAst (Axiom name _) did) ->
      pure (C.MetaConst did cSig)
    PDDecl (DeclAst (Prove _) did) -> do
      vSig <- eval cSig
      bs <- unBindings <$> ask
      let
        gDids =
          flip filterMap (fromList . toList $ bs) \case
            BGlobal gDid -> Just gDid
            _ -> Nothing
      gTys <-
        traverse
          (\gDid -> do
            (ty, _) <- declType gDid
            eval ty)
          gDids
      substs <- proveDet gTys vSig
      case substs of
        Nothing -> errorDecl (FailedProve vSig)
        Just substs ->
          if isAmbiguous substs then
            errorDecl (AmbiguousProve vSig substs)
          else do
            putTypeUVSols (concat substs)
            pure (C.MetaConst did cSig)
      where
        isAmbiguous :: Seq Substitution -> Bool
        isAmbiguous substs =
          let
            substs' =
              mapWithIndex (,) .
              filter (not . Set.null) .
              fmap
                (Set.filter \case
                  LVGlobal _ -> False
                  UVGlobal _ -> True) .
              fmap Map.keysSet $
              substs
          in
            not .
            all (uncurry Set.disjoint) $
            [(x, y) | (i1, x) <- substs', (i2, y) <- substs', i1 /= i2]
    PDDecl (DeclAst (Fresh name _) did@(Id n)) ->
      pure (C.MetaTerm did cSig (C.UniVar (UVGlobal n)))
    PDConstr conUniv constr@(ConstrAst (Constr _ _) did dtDid) -> do
      unify univ (N.TypeType (convertUniv conUniv))
      pure (constDecl conUniv did cSig)
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
withPos' act (PDConstr univ (SourcePos ast pos)) = withPos pos (act (PDConstr univ ast))
withPos' act pd = act pd

declType :: HasCallStack => Query sig m => Id -> m (C.Term, N.Term)
declType did = memo (DeclType did) $ withDecl did $ withPos' $ \decl ->
  case decl of
    PDDecl (DeclAst (ObjTerm name sig def) _) -> EE.checkObjType sig
    PDDecl (DeclAst (MetaTerm name sig def) _) -> EE.checkMetaType sig
    PDDecl (DeclAst (Datatype name sig _) _) -> EE.checkObjType sig -- TODO: Form check
    PDDecl (DeclAst (Axiom name sig) _) -> EE.checkMetaType sig
    PDDecl (DeclAst (Prove sig) _) -> EE.checkMetaType sig
    PDDecl (DeclAst (Fresh name sig) _) -> EE.checkMetaType sig
    PDDecl (DeclAst (CFun _ (fmap snd -> inTys) outTy _) _) -> do
      cInTys <- traverse (flip EE.check (N.TypeType (N.Low C))) inTys
      cOutTy <- EE.check outTy (N.TypeType (N.Low C))
      pure (C.Rigid (C.CFunType cInTys cOutTy), N.TypeType (N.Low C))
    PDConstr univ constr@(ConstrAst (Constr _ sig) _ _) ->
      (,) <$> EE.check sig (N.TypeType (convertUniv univ)) <*> pure (N.TypeType (convertUniv univ)) -- TODO: Form check