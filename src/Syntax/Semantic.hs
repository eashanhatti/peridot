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

envSize :: Environment -> Natural
envSize (Env locals _) = fromIntegral (length locals)

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
  | RecIntro (Seq (Field, Closure))
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
    "(ObjFunType " ++ show pm ++ " " ++ show inTy ++ " (" ++ show outTy ++ "))"
  show (ObjFunIntro body) = "(ObjFunIntro (" ++ show body ++ "))"
  show (MetaFunType pm inTy outTy) =
    "(MetaFunType " ++ show pm ++ " " ++ show inTy ++ " (" ++ show outTy ++ "))"
  show (MetaFunIntro body) = "(MetaFunIntro (" ++ show body ++ "))"
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

type Redex = RedexF Term

data RedexF a
  = MetaFunElim a a
  | ObjFunElim a a
  | CodeObjElim a
  | GlobalVar a Bool
  | UniVar Global (Maybe a)
  | TwoElim a a a
  | RecElim a Field
  | SingElim a
  | Declare Universe a a a
  | Define a a a
  | TextElimCat a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

viewFunType :: Term -> Maybe (PassMethod, Term, Closure)
viewFunType (MetaFunType pm inTy outTy) = Just (pm, inTy, outTy)
viewFunType (ObjFunType pm inTy outTy) = Just (pm, inTy, outTy)
viewFunType _ = Nothing

viewImFunType :: Term -> Maybe (Term, Closure)
viewImFunType (MetaFunType Unification inTy outTy) = Just (inTy, outTy)
viewImFunType (ObjFunType Unification inTy outTy) = Just (inTy, outTy)
viewImFunType _ = Nothing

pattern FunType pm inTy outTy <- (viewFunType -> Just (pm, inTy, outTy))

viewMetaFunElims :: Term -> Maybe (Term, Seq Term)
viewMetaFunElims (Neutral _ (ObjFunElim _ _)) = Nothing
viewMetaFunElims (Neutral _ (MetaFunElim lam arg)) = do
  (lam', args) <- viewMetaFunElims lam
  pure (lam', args |> arg)
viewMetaFunElims term = pure (term, mempty)

viewObjFunElims :: Term -> Maybe (Term, Seq Term)
viewObjFunElims (Neutral _ (MetaFunElim _ _)) = Nothing
viewObjFunElims (Neutral _ (ObjFunElim lam arg)) = do
  (lam', args) <- viewObjFunElims lam
  pure (lam', args |> arg)
viewObjFunElims term = pure (term, mempty)

viewName :: Term -> Maybe Id
viewName (Rigid (NameIntro _ did)) = Just did
viewName _ = Nothing

pattern MetaFunElims lam args <- (viewMetaFunElims -> Just (lam, args))

pattern ObjTypeType = Rigid (TypeType Obj)
pattern MetaTypeType = Rigid (TypeType Meta)

tmUniv :: Term -> Maybe Universe
tmUniv (ObjFunType _ _ _) = Just Obj
tmUniv (RecType _) = Just Obj
tmUniv (MetaFunType _ _ _) = Just Meta
tmUniv (Rigid TwoType) = Just Obj
tmUniv (Rigid (SingType _ _)) = Just Obj
tmUniv (Rigid (ObjIdType _ _)) = Just Obj
tmUniv (Rigid (NameType _ _)) = Just Meta
tmUniv (Rigid (CodeObjType _)) = Just Meta
tmUniv (Rigid TextType) = Just Meta
tmUniv (Rigid (ImplType _ _)) = Just Meta
tmUniv (Rigid (ConjType _ _)) = Just Meta
tmUniv (Rigid (DisjType _ _)) = Just Meta
tmUniv (Rigid (TypeType u)) = Just u
tmUniv (Neutral _ (MetaFunElim _ _)) = Just Meta
tmUniv (Neutral _ (ObjFunElim _ _)) = Just Obj
tmUniv (Neutral _ (CodeObjElim _)) = Just Obj
tmUniv (Neutral _ (UniVar _ (Just MetaTypeType))) = Just Meta
tmUniv (Neutral _ (UniVar _ (Just ObjTypeType))) = Just Obj
tmUniv (Neutral _ (TwoElim _ _ _)) = Just Obj
tmUniv (Neutral _ (RecElim _ _)) = Just Obj
tmUniv (Neutral _ (SingElim _)) = Just Obj
tmUniv (Neutral _ (TextElimCat _ _)) = Just Meta
tmUniv _ = Nothing
