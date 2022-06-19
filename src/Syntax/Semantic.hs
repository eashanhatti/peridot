{-# LANGUAGE PatternSynonyms #-}
module Syntax.Semantic
( module Syntax.Semantic
, module Syntax.Common
) where

import Syntax.Common hiding(Declaration)
import Syntax.Common qualified as Cm
import Syntax.Core qualified as C
import Data.Map(Map, insert)
import Data.Sequence
import Prelude hiding(length, zip, map)
import {-# SOURCE #-} Normalization
import Control.Carrier.Reader
import Data.Functor.Identity
import Data.Text qualified as Text
import Shower
import Numeric.Natural

data Environment = Env
  { unLocals :: Seq Term
  , unGlobals :: Map Id Term }
  deriving (Eq)

withLocal :: Term -> Environment -> Environment
withLocal def (Env locals globals) = Env (def <| locals) globals

withGlobal :: Id -> Term -> Environment -> Environment
withGlobal did def (Env locals globals) = Env locals (insert did def globals)

envSize :: Environment -> Int
envSize (Env locals _) = length locals

instance Show Environment where
  show (Env locals _) = show locals

data Closure = Clo Environment C.Term
  deriving (Eq, Show)

type Type = Term

data Term
  -- Object level
  = ObjFunType PassMethod Term Closure
  | ObjFunIntro Closure
  | RecType (Seq (Field, Closure))
  | RecIntro (Seq (Field, Term))
  -- Meta level
  | MetaFunType PassMethod Term Closure
  | MetaFunIntro Closure
  -- Other
  | LocalVar Level
  | Rigid (RigidTerm Term)
  -- If `Nothing`, the term is stuck
  | Neutral (ReaderC NormContext Identity (Maybe Term)) Redex

instance Show Term where
  show (ObjFunType pm inTy outTy) =
    "(ObjFunType " ++ show pm ++ " " ++ show inTy ++ " " ++ show outTy ++ ")"
  show (ObjFunIntro body) = "(ObjFunIntro " ++ show body ++ ")"
  show (MetaFunType pm inTy outTy) =
    "(MetaFunType " ++ show pm ++ " " ++ show inTy ++ " " ++ show outTy ++ ")"
  show (MetaFunIntro body) = "(MetaFunIntro " ++ show body ++ ")"
  show (LocalVar lvl) = "(LocalVar " ++ show lvl ++ ")"
  show (RecType tys) = "(RecType " ++ show tys ++ ")"
  show (RecIntro tys) = "(RecIntro " ++ show tys ++ ")"
  show (Rigid term) = "(Rigid (" ++ show term ++ "))"
  show (Neutral _ redex) = "(Neutral _ (" ++ show redex ++ "))"

instance Eq Term where
  ObjFunType pm1 inTy1 outTy1 == ObjFunType pm2 inTy2 outTy2 =
    pm1 == pm2 && inTy1 == inTy2 && outTy1 == outTy2
  ObjFunIntro body1 == ObjFunIntro body2 = body1 == body2
  RecType tys1 == RecType tys2 =
    length tys1 == length tys2 &&
    (and . fmap (\(ty1, ty2) -> ty1 == ty2) $ zip tys1 tys2)
  RecIntro defs1 == RecIntro defs2 =
    length defs1 == length defs2 &&
    (and . fmap (\(def1, def2) -> def1 == def2) $ zip defs1 defs2)
  MetaFunType pm1 inTy1 outTy1 == MetaFunType pm2 inTy2 outTy2 =
    pm1 == pm2 && inTy1 == inTy2 && outTy1 == outTy2
  MetaFunIntro body1 == MetaFunIntro body2 = body1 == body2
  LocalVar l1 == LocalVar l2 = l1 == l2
  Rigid r1 == Rigid r2 = r1 == r2
  Neutral _ redex1 == Neutral _ redex2 = redex1 == redex2
  _ == _ = False

data Redex
  = MetaFunElim Term Term
  | ObjFunElim Term Term
  | ObjConstElim (Map Id Term)
  | CodeObjElim Term
  | CodeCElim Term
  | GlobalVar Term
  | UniVar Global
  | TwoElim Term Term Term
  | RecElim Term Field
  | SingElim Term
  | Declare Universe Term Term Term
  | Define Term Term Term
  | TextElimCat Term Term
  deriving (Eq, Show)

viewFunType :: Term -> Maybe (PassMethod, Term, Closure)
viewFunType (MetaFunType pm inTy outTy) = Just (pm, inTy, outTy)
viewFunType (ObjFunType pm inTy outTy) = Just (pm, inTy, outTy)
viewFunType _ = Nothing

pattern FunType pm inTy outTy <- (viewFunType -> Just (pm, inTy, outTy))

viewMetaFunElims :: Term -> (Term, Seq Term)
viewMetaFunElims (Neutral _ (MetaFunElim lam arg)) =
  let (lam', args) = viewMetaFunElims lam
  in (lam', args |> arg)
viewMetaFunElims term = (term, mempty)

viewName :: Term -> Maybe Id
viewName (Rigid (NameIntro _ did)) = Just did
viewName _ = Nothing

pattern MetaFunElims lam args <- (viewMetaFunElims -> (lam, args))

pattern ObjTypeType = Rigid (TypeType Obj)
pattern MetaTypeType = Rigid (TypeType Meta)
