{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Surface where

import Data.Map(Map)
import Data.Set(Set)

data Name = UnfocusedName String | FocusedName String
  deriving (Show, Eq, Ord)

pattern Name s <- (unName -> s) where
  Name s = UnfocusedName s

unName name = case name of
  UnfocusedName s -> s
  FocusedName s -> s

data GName = UnfocusedGName [String] | FocusedGName [String]
  deriving (Show, Eq, Ord)

pattern GName ns <- (unGName -> ns) where
  GName ns = UnfocusedGName ns

unGName name = case name of
  UnfocusedGName ns -> ns
  FocusedGName ns -> ns

data Direction = Left | Right
  deriving (Eq, Show)

data Item
  = NamespaceDef Name [Item]
  | TermDef Name Term Term -- name, dec, def
  | IndDef Name Term [(Name, Term)] -- name, dec, constructors
  | ProdDef Name Term [Term]
  | EditorBlankDef
  | EditorFocusDef Item Direction
  deriving (Show, Eq)

data ItemPart = Dec | Def
  deriving (Eq, Ord, Show)

data Term
  = Var Name
  | GVar GName
  | Lam [Name] Term
  | App Term [Term]
  | Ann Term Term
  | Pi Name Term Term
  | Let Name Term Term Term
  | U0
  | U1
  | Code Term
  | Quote Term
  | Splice Term
  | MkInd GName [Term]
  | MkProd Term [Term]
  | Hole
  | EditorBlank
  | EditorFocus Term Direction
  deriving (Show, Eq)