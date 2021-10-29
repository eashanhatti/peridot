module Var where

newtype Index = Index { unIndex :: Int } deriving (Show, Eq, Ord)

newtype Global = Global { unGlobal :: Int } deriving (Show, Eq, Ord)

newtype Level = Level { unLevel :: Int } deriving (Show, Eq, Ord)

incLevel lv = (Level $ unLevel lv + 1)

incLevelN :: Int -> Level -> Level
incLevelN n = case n of
	0 -> id
	n -> incLevel . (incLevelN (n - 1))

data Id = Id { unId :: Int } deriving (Show, Eq, Ord)