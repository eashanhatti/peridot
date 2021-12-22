{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Surface where

import Data.Map(Map)
import Data.Set(Set)
import Data.Data(Data)

data Name = UnfocusedName String | FocusedName String Direction
  deriving (Show, Eq, Ord, Data)

pattern Name s <- (unName -> s) where
  Name s = UnfocusedName s

unName name = case name of
  UnfocusedName s -> s
  FocusedName s _ -> s

data GName = UnfocusedGName [String] | FocusedGName [String]
  deriving (Show, Eq, Ord, Data)

pattern GName ns <- (unGName -> ns) where
  GName ns = UnfocusedGName ns

unGName name = case name of
  UnfocusedGName ns -> ns
  FocusedGName ns -> ns

data Constructor = FocusedConstructor Name Term | UnfocusedConstructor Name Term | EditorBlankCon
  deriving (Show, Eq, Data)

pattern Constructor n t <- (unCon -> (n, t)) where
  Constructor n t = UnfocusedConstructor n t

unCon con = case con of
  UnfocusedConstructor n t -> (n, t)
  FocusedConstructor n t -> (n, t)

data Direction = Left | Right
  deriving (Eq, Ord, Show, Data)

data Item
  = NamespaceDef Name [Item]
  | TermDef Name Term Term -- name, dec, def
  | IndDef Name Term [Constructor] -- name, dec, constructors
  | ProdDef Name Term [Term]
  | EditorBlankDef
  | EditorFocusDef Item Direction
  deriving (Show, Eq, Data)

data ItemPart = Dec | Def
  deriving (Eq, Ord, Show)

data Pattern
  = BindingPat String
  | ConPat GName [Pattern]
  | EditorFocusPat Pattern
  | EditorBlankPat
  deriving (Show, Eq, Data)

data Clause = UnfocusedClause Pattern Term | FocusedClause Pattern Term | EditorBlankClause
  deriving (Show, Eq, Data)

pattern Clause p t <- (unClause -> (p, t)) where
  Clause p t = UnfocusedClause p t

unClause clause = case clause of
  UnfocusedClause p t -> (p, t)
  FocusedClause p t -> (p, t)

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
  | Match [Term] [Clause]
  | Hole
  | EditorBlank
  | EditorFocus Term Direction
  deriving (Show, Eq, Data)