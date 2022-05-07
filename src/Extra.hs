module Extra where

import Data.Map qualified as Map
import Shower
import Data.Maybe
import Data.Sequence
import Prelude hiding(concatMap)

fromRight :: Either () a -> a
fromRight (Right x) = x

(!) :: (Ord k, Show k, Show v) => Map.Map k v -> k -> v
(!) m k = case Map.lookup k m of
  Just v -> v
  Nothing -> error $ "MAP LOOKUP: " ++ shower (k, m)

justs = Map.map fromJust . Map.filter isJust

concatMap :: (a -> Seq b) -> Seq a -> Seq b
concatMap f Empty = Empty
concatMap f (x :<| xs) = f x <> concatMap f xs

head :: Seq a -> a
head (x :<| _) = x

tail :: Seq a -> Seq a
tail (_ :<| xs) = xs

filterTraverse :: Monad m => (a -> m (Maybe b)) -> Seq a -> m (Seq b)
filterTraverse f Empty = pure Empty
filterTraverse f (x :<| xs) = do
  x' <- f x
  case x' of
    Just y -> (y <|) <$> filterTraverse f xs
    Nothing -> filterTraverse f xs
