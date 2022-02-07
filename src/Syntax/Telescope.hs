module Syntax.Telescope where

data Telescope a
  = Empty
  | Bind a (Telescope a)
  deriving (Foldable, Eq)