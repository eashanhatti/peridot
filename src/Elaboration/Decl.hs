module Elaboration.Decl where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Telescope qualified as T
import Syntax.Extra
import Elaboration.Effect
import Data.Map qualified as Map
import {-# SOURCE #-} Elaboration.Term qualified as EE
import Elaboration.Telescope qualified as ET
import Normalization
import Control.Monad
import Data.Foldable(toList)

check :: Elab sig m => Predeclaration -> m C.Declaration
check decl = memo (CheckDecl decl) case decl of
  PDDecl (DeclAst (Term name sig def) did) -> do
    stage <- freshStageUV
    cSig <- EE.check sig (N.TypeType stage)
    cDef <- eval cSig >>= EE.check def
    pure (C.Term did cSig cDef)
  PDDecl (DeclAst (Datatype name tele constrs) did) -> do
    (cTele, _) <- ET.check tele (N.TypeType Object)
    pure (C.Datatype did cTele)
  PDDecl (DeclAst (Axiom name sig) did) ->
    C.Axiom did <$> EE.check sig (N.TypeType Meta)
  PDDecl (DeclAst (Prove sig) did) ->
    C.Prove did <$> EE.check sig (N.TypeType Meta)
  PDDecl (DeclAst (Fresh name sig) did) ->
    C.Fresh did <$> EE.check sig (N.TypeType Meta)
  PDConstr constr@(ConstrAst (Constr _ tele args) did dtDid) -> do
    C.Datatype _ dtTele <- getDecl dtDid >>= check
    (cTele, names) <- ET.check tele (N.TypeType Object)
    if T.size dtTele /= fromIntegral (length args) then do
      report (WrongAppArity (T.size dtTele) (fromIntegral (length args)))
      pure C.DElabError
    else do
      cArgs <- checkArgs dtTele args
      pure (C.Constr did cTele dtDid cArgs)
    where
      checkArgs :: Elab sig m => C.Telescope -> [TermAst] -> m [C.Term]
      checkArgs T.Empty [] = pure []
      checkArgs (T.Bind ty tele) (arg:args) = do
        vTy <- eval ty
        cArg <- EE.check arg vTy
        vArg <- eval cArg
        cArgs <- define vArg (checkArgs tele args)
        pure (cArg:cArgs)

declType :: Elab sig m => Id -> m N.Term
declType did = memo (DeclType did) do
  cDecl <- getDecl did >>= check
  case cDecl of
    C.Datatype _ _ -> pure (N.TypeType Object)
    C.Constr _ _ did args -> N.DatatypeType did <$> evalArgs args
    C.Term _ sig _ -> eval sig
    C.Axiom _ _ -> pure (N.TypeType Meta)
    C.Prove _ sig -> eval sig
    C.Fresh _ sig -> eval sig
    C.DElabError -> pure N.EElabError
  where
    evalArgs :: Elab sig m => [C.Term] -> m [N.Term]
    evalArgs [] = pure []
    evalArgs (arg:args) = do
      vArg <- eval arg
      vArgs <- define vArg (evalArgs args)
      pure (vArg:vArgs)