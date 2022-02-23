module Elaboration.Decl where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Extra
import Elaboration.Effect
import Data.Map qualified as Map
import {-# SOURCE #-} Elaboration.Term qualified as EE
import Normalization
import Control.Monad
import Data.Foldable(toList, foldl')

check :: Elab sig m => Predeclaration -> m C.Declaration
check decl = memo (CheckDecl decl) case decl of
  PDDecl (DeclAst (Term name sig def) did) -> do
    stage <- freshStageUV
    cSig <- EE.check sig (N.TypeType stage)
    cDef <- eval cSig >>= EE.check def
    pure (C.Term did cSig cDef)
  PDDecl (DeclAst (Datatype name sig _) did) -> do
    cSig <- EE.check sig (N.TypeType Object)
    pure (C.Datatype did cSig)
  PDDecl (DeclAst (Axiom name sig) did) ->
    C.Axiom did <$> EE.check sig (N.TypeType Meta)
  PDDecl (DeclAst (Prove sig) did) -> do
    cSig <- EE.check sig (N.TypeType Meta)
    proof <- eval cSig >>= buildProof
    pure (C.Term did cSig proof)
  PDDecl (DeclAst (Fresh name sig) did) ->
    C.Fresh did <$> EE.check sig (N.TypeType Meta)
  PDConstr constr@(ConstrAst (Constr _ sig) did dtDid) -> do
    cSig <- EE.check sig (N.TypeType Meta)
    -- TODO: Form check
    pure (C.Constr did cSig)

buildProof :: Elab sig m => N.Term -> m C.Term
buildProof = undefined

declType :: Elab sig m => Id -> m N.Term
declType did = memo (DeclType did) do
  cDecl <- getDecl did >>= check
  case cDecl of
    C.Datatype _ _ -> pure (N.TypeType Object)
    C.Constr _ _ -> undefined
    C.Term _ sig _ -> eval sig
    C.Axiom _ sig -> eval sig
    C.Fresh _ sig -> eval sig
    C.DElabError -> pure N.EElabError
  where
    evalArgs :: Elab sig m => [C.Term] -> m [N.Term]
    evalArgs [] = pure []
    evalArgs (arg:args) = do
      vArg <- eval arg
      vArgs <- define vArg (evalArgs args)
      pure (vArg:vArgs)