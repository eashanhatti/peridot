module Surface where

import Core(Stage)

data Span = Span
  deriving Show

data Name = Name String
  deriving (Show, Eq, Ord)

data Term
  = Spanned Term Span
  | Var Name
  | Lam Name Term
  | App Term Term
  | Ann Term Term
  | Pi Name Term Term
  | QuoteType Term Stage
  | Let Name Term Term Term
  | Universe
  | Hole
  deriving Show