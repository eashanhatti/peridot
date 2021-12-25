module Var where

newtype Index = Index { unIndex :: Int } deriving (Eq, Ord)

instance Show Index where
  show (Index ix) = "index" ++ show ix

incIndex ix = Index $ unIndex ix + 1

newtype Global = Global { unGlobal :: Int } deriving (Eq, Ord)

instance Show Global where
  show (Global gl) = "global" ++ show gl

newtype Level = Level { unLevel :: Int } deriving (Eq, Ord)

instance Show Level where
  show (Level lv) = "level" ++ show lv


incLevel lv = Level $ unLevel lv + 1

incLevelN :: Int -> Level -> Level
incLevelN n = case n of
  0 -> id
  n -> incLevel . (incLevelN (n - 1))

data Id = Id { unId :: Int } deriving (Eq, Ord)

instance Show Id where
  show (Id nid) = "id" ++ show nid