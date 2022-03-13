module Unification where

import Syntax.Semantic

data Substitution

unify :: Monad m => Term -> Term -> m (Maybe Substitution)
