module Elaboration.Error where

data InnerError

instance Eq InnerError where

data Error

instance Eq Error where

instance Show Error where