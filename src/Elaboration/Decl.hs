module Elaboration.Decl where

import Syntax.Surface
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Telescope qualified as T
import Syntax.Variable
import Syntax.Stage
import Elaboration.Effect
import Data.Map qualified as Map
import {-# SOURCE #-} Elaboration.Term qualified as EE
import Elaboration.Telescope qualified as ET
import Normalization
import Control.Monad
import Data.Foldable(toList)

check :: Elab sig m => Predeclaration -> m C.Declaration
check decl = memo (ElabDecl decl) case decl of
    PDDecl (DeclAst (Term name sig def) did) -> do
      stage <- freshStageUV
      cSig <- EE.check sig (N.TypeType stage)
      cDef <- eval cSig >>= EE.check def
      pure (C.Term cSig cDef)
    PDDecl (DeclAst (Datatype name tele constrs) did) -> do
      stage <- freshStageUV
      (cTele, _) <- ET.check tele (N.TypeType stage)
      pure (C.Datatype did cTele stage)
    PDConstr constr@(ConstrAst (Constr _ tele args) did dtDid) -> do
      C.Datatype _ dtTele stage <- getDecl dtDid >>= check
      (cTele, names) <- ET.check tele (N.TypeType stage)
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