module Surface where

data Span = Span Int Int
  deriving Show

data Name = Name String
  deriving Show

data Term
  = Spanned Term Span
  | Var Name
  | Lam Name Term
  | App Term Term
  | Pi Name Term Term
  | Let Name Term Term Term
  | Universe
  | Hole
  deriving Show