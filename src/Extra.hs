module Extra where

fromRight :: Either () a -> a
fromRight (Right x) = x
