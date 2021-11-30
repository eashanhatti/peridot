{-# LANGUAGE LambdaCase #-}

module Core where

import Var
import {-# SOURCE #-} qualified Norm as N
import Surface(Direction)
import Control.Monad.Reader(Reader, ask)
import Data.Map(Map)
import Data.Set(Set)
import Data.List(intersperse)
import Numeric.Natural
import Debug.Trace(trace)
import Data.Maybe(isJust)
import Etc

data BinderInfo = Abstract | Concrete
  deriving (Show, Eq)

-- type annotation
type Type = Term

data HoleName = HoleName Int
  deriving (Show, Eq)

data Program = Program [Item]
  deriving Show

data IndDefInfo = IndDefInfo [String]
  deriving Show

data Item
  = TermDef Id Term
  | IndDef Id Type IndDefInfo
  | ProdDef Id Type [Type]
  | ConDef Id Type
  | ElabBlankItem Id Type

instance Show Item where
  show item = case item of
    TermDef nid body -> "def " ++ show nid ++ " = " ++ show body
    IndDef nid ty _ -> "ind " ++ show nid ++ " : " ++ show ty
    ProdDef nid ty fields -> "prod " ++ show nid ++ " : " ++ show ty ++ "[" ++ (concat $ intersperse ", " $ map show fields) ++ "]"
    ConDef nid ty -> "con " ++ show nid ++ " : " ++ show ty
    ElabBlankItem nid _ -> "blank " ++ show nid

itemId item = case item of
  TermDef nid _ -> nid
  IndDef nid _ _ -> nid
  ConDef nid _ -> nid
  ProdDef nid _ _ -> nid
  ElabBlankItem nid _ -> nid

data FunIntroInfo = FunIntroInfo Natural String
  deriving Eq
data FunTypeInfo = FunTypeInfo String
  deriving Eq
data FunElimInfo = FunElimInfo Natural
  deriving Eq
data VarInfo = VarInfo String
  deriving Eq
data GVarInfo = GVarInfo [String]
  deriving Eq
data Info = Info (Maybe Direction)
  deriving Eq

data Term = Term
  { unInfo :: Info
  , unTerm :: TermInner }
  deriving Eq

gen e = trace ("TRACE " ++ show (Term (Info Nothing) e)) $ Term (Info Nothing) e

data TermInner
  = Var Index Type VarInfo
  | GVar Id Type GVarInfo
  | TypeType0
  | TypeType1
  | FunIntro Term Type FunIntroInfo
  | FunType Term Term FunTypeInfo
  | FunElim Term Term FunElimInfo
  | QuoteType Term
  | QuoteIntro Term Type
  | QuoteElim Term
  | IndType Id [Term]
  | IndIntro Id [Term] Type
  | ProdType Id [Term]
  | ProdIntro Type [Term]
  | Letrec [Term] Term
  | Meta Global (Maybe Type)
  | InsertedMeta [BinderInfo] Global (Maybe Type)
  | ElabError
  deriving Eq

instance Show TermInner where
  show term = case term of
    Var ix ty _ -> "i" ++ show (unIndex ix)
    TypeType0 -> "U0"
    TypeType1 -> "U1"
    FunIntro body ty _ -> "{" ++ show body ++ "}"
    FunType inTy outTy _ -> show inTy ++ " -> " ++ show outTy
    FunElim lam arg _ -> "(" ++ show lam ++ " @ " ++ show arg ++ ")"
    QuoteType innerTy -> "Quote " ++ show innerTy
    QuoteIntro inner _ -> "<" ++ show inner ++ ">"
    QuoteElim quote -> "[" ++ show quote ++ "]"
    Letrec defs body -> "letrec " ++ show defs ++ " in " ++ show body
    Meta gl ty ->
      -- if showTys then
        "(?" ++ show (unGlobal gl) ++ " : " ++ show ty ++ ")"
      -- else
      --   "?" ++ show (unGlobal gl)
    InsertedMeta bis gl ty ->
      let
        sty = "_"
          -- case ty of
          --   InsertedMeta _ gl' _ | gl == gl' -> "_"
          --   _ -> show ty
      in "(?" ++ show (unGlobal gl) ++ " : " ++ sty ++ ";" ++ (show $ Prelude.map show bis) ++ ")"
    GVar nid ty _ -> "(g" ++ show (unId nid) ++ ":" ++ show ty ++ ")"
    IndIntro nid args ty -> "#" ++ show nid ++ "[" ++ (concat $ intersperse ", " $ Prelude.map show args) ++ "]" ++ ":" ++ show ty
    IndType nid indices -> "Ind" ++ show nid ++ "[" ++ (concat $ intersperse ", " $ Prelude.map show indices) ++ "]"
    ProdIntro ty fields -> "{" ++ (concat $ intersperse ", " $ Prelude.map show fields) ++ "}" ++ ":" ++ show ty
    ProdType nid indices -> "Prod" ++ show nid ++ "[" ++ (concat $ intersperse ", " $ Prelude.map show indices) ++ "]"
    ElabError -> "<error>"

-- shift :: Set Index -> Term -> Reader Int Term
-- shift bounds = \case
--   Var ix ty ->
--     if ix `member` bounds then
--       pure $ Var ix ty
--     else do
--       amt <- ask
--       pure $ Var (Index $ unIndex ix + amt) ty
--   TypeType -> pure TypeType
--   FunIntro body ty -> FunIntro <$> shift next body <*> shift bounds ty
--   FunType inTy outTy -> FunType <$> shift bounds inTy <*> shift next outTy
--   FunElim lam arg -> FunElim <$> shift bounds lam <*> shift bounds arg
--   Let def defTy body -> Let <$> shift bounds def <*> shift bounds defTy <*> shift next body
--   Meta gl ty -> Meta <$> pure gl <*> shift bounds ty
--   InsertedMeta bis gl ty -> InsertedMeta <$> pure bis <*> pure gl <*> shift bounds ty
--   ElabError -> pure ElabError
--   _ -> error "Unimplemented"
--   where
--     next :: Set Index
--     next = insert (Index 0) $ Data.Set.map (\ix -> Index $ unIndex ix + 1) bounds

instance Show Term where
  show (Term (Info m) term) = show (isJust m) ++ show term