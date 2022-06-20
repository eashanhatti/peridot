module Elaboration.Declaration where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Common hiding(Declaration(..), Universe(..))
import Elaboration.Effect
import Control.Effect.Reader
import Control.Effect.State
import Control.Carrier.NonDet.Church hiding(Empty)
import Data.Map qualified as Map
import Data.Set qualified as Set
import {-# SOURCE #-} Elaboration.Term qualified as EE
import Normalization hiding(eval)
import Control.Monad
import Control.Monad.Extra
import Data.Foldable(toList, foldl')
import Data.Traversable
import GHC.Stack
import Data.Sequence
import Search(Substitution, concatSubsts)
import Prelude hiding(traverse, map, zip, concat, filter, mapWithIndex)
import Debug.Trace
import Extra

check :: HasCallStack => Query sig m => Id -> m C.Term
check did = memo (CheckDecl did) $ withDecl did $ withPos' $ \decl -> do
  (cSig, univ) <- declType (unPDDeclId decl)
  case decl of
    PDDecl (DeclAst (ObjTerm name _ def) did) -> do
      cDef <- eval cSig >>= EE.check def
      pure cDef
    PDDecl (DeclAst (MetaTerm name _ def) did) -> do
      cDef <- eval cSig >>= EE.check def
      pure cDef
    PDDecl (DeclAst (Axiom name _) did) ->
      pure (C.Rigid (C.MetaConstIntro did))
    PDDecl (DeclAst (Prove _) did) -> do
      vSig <- eval cSig
      bs <- unBindings <$> ask
      axioms <- unAxioms <$> ask
      let
        gDids =
          flip filterMap (fromList . toList $ bs) \case
            BGlobal gDid | Set.member gDid axioms -> Just gDid
            _ -> Nothing
      gTys <-
        traverse
          (\gDid -> do
            (ty, _) <- declType gDid
            eval ty)
          gDids
      -- let !_ = tracePretty gTys
      substs <- proveDet gTys vSig
      case substs of
        Nothing -> do
          report (FailedProve cSig vSig gTys)
          pure (C.Rigid C.ElabError)
        Just substs ->
          if isAmbiguous substs then do
            report (AmbiguousProve cSig substs)
            pure (C.Rigid C.ElabError)
          else do
            let (ts, eqs) = concatSubsts substs
            putTypeUVSols ts
            putUVEqs eqs
            pure (C.Rigid (C.MetaConstIntro did))
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
              fmap Map.keysSet .
              fmap fst $
              substs
          in
            not .
            all (uncurry Set.disjoint) $
            [(x, y) | (i1, x) <- substs', (i2, y) <- substs', i1 /= i2]
    PDDecl (DeclAst (Fresh name _) did@(Id n)) -> do
      modify (\st -> st { unLogvars = Set.insert did (unLogvars st) })
      pure (C.UniVar (UVGlobal n))
    PDDecl (DeclAst (Output path text) _) -> do
      cText <- EE.check text (N.Rigid N.TextType)
      vText <- eval cText
      modify (\st -> st { unOutputs = (path, vText) <| unOutputs st })
      pure (C.Rigid C.Dummy)

withPos' ::
  HasCallStack => Elab sig m =>
  (Predeclaration -> m a) ->
  (Predeclaration -> m a)
withPos' act (PDDecl (SourcePos ast pos)) = withPos pos (act (PDDecl ast))
withPos' act pd = act pd

declType :: HasCallStack => Query sig m => Id -> m (C.Term, N.Universe)
declType did = memo (DeclType did) $ withDecl did $ withPos' $ \decl -> asType
  case decl of
    PDDecl (DeclAst (ObjTerm name sig def) _) -> EE.checkObjType sig
    PDDecl (DeclAst (MetaTerm name sig def) _) -> EE.checkMetaType sig
    PDDecl (DeclAst (Axiom name sig) _) -> EE.checkMetaType sig
    PDDecl (DeclAst (Prove sig) _) -> EE.checkMetaType sig
    PDDecl (DeclAst (Fresh name sig) (Id n)) -> do
      modify (\st -> st { unLogvarNames = Map.insert (UVGlobal n) (unName name) (unLogvarNames st) })
      EE.checkMetaType sig
    PDDecl (DeclAst (Output _ _) _) -> pure (C.Rigid C.Dummy, N.Meta)