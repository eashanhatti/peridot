module Surface where

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
  | Let Name Term Term Term
  | Universe
  | Hole
  deriving Show