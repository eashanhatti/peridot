module Extra where

import Data.Map qualified as Map
import Shower
import Data.Maybe
import Data.Sequence
import Debug.Trace
import Prelude hiding(concatMap, concat)

fromRight :: Either () a -> a
fromRight (Right x) = x

(!) :: (Ord k, Show k, Show v) => Map.Map k v -> k -> v
(!) m k = case Map.lookup k m of
  Just v -> v
  Nothing -> error $ "MAP LOOKUP: " ++ shower (k, m)

justs = Map.map fromJust . Map.filter isJust

concat :: Monoid a => Seq a -> a
concat Empty = mempty
concat (x :<| xs) = x <> concat xs

concatMap :: Monoid b => (a -> b) -> Seq a -> b
concatMap f Empty = mempty
concatMap f (x :<| xs) = f x <> concatMap f xs

head :: Seq a -> a
head (x :<| _) = x

tail :: Seq a -> Seq a
tail (_ :<| xs) = xs

filterMap :: (a -> Maybe b) -> Seq a -> Seq b
filterMap f Empty = Empty
filterMap f ((f -> Just y) :<| xs) = y <| filterMap f xs
filterMap f (_ :<| xs) = filterMap f xs

filterTraverse :: Monad m => (a -> m (Maybe b)) -> Seq a -> m (Seq b)
filterTraverse f Empty = pure Empty
filterTraverse f (x :<| xs) = do
  x' <- f x
  case x' of
    Just y -> (y <|) <$> filterTraverse f xs
    Nothing -> filterTraverse f xs

allJustOrNothing (Just x :<| xs) = (x <|) <$> allJustOrNothing xs
allJustOrNothing (Nothing :<| _) = Nothing
allJustOrNothing Empty = Just Empty

traceWith :: (a -> String) -> a -> a
traceWith f x = trace (f x) x
