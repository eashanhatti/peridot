module Var where

newtype Index = Index { unIndex :: Int } deriving (Show, Eq, Ord)

newtype Global = Global { unGlobal :: Int } deriving (Show, Eq, Ord)

newtype Level = Level { unLevel :: Int } deriving (Show, Eq, Ord)

incLevel lv = (Level $ unLevel lv + 1)