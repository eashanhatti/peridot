module Extra where

import Data.Map qualified as Map
import Shower
import Data.Maybe
import Data.Sequence
import Debug.Trace
import Data.Functor.Identity
import Prelude hiding(concatMap, concat, filter, null, length)

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

concatMapM :: (Monad m, Monoid b) => (a -> m b) -> Seq a -> m b
concatMapM f Empty = pure mempty
concatMapM f (x :<| xs) = (<>) <$> f x <*> concatMapM f xs

duplicates :: forall a. Show a =>Eq a => Seq a -> Seq a
duplicates xs = filter go xs where
  go :: a -> Bool
  go x = (>2) . length . filter (==x) $ xs

concatMap :: Monoid b => (a -> b) -> Seq a -> b
concatMap f = runIdentity . concatMapM (Identity . f)

head :: Seq a -> a
head (x :<| _) = x
head _ = error "error: `head`"

tail :: Seq a -> Seq a
tail (_ :<| xs) = xs
tail _ = error "error: `tail`"

filterMapM :: Monad m => (a -> m (Maybe b)) -> Seq a -> m (Seq b)
filterMapM f Empty = pure Empty
filterMapM f (x :<| xs) = do
  r <- f x
  case r of
    Just y -> (y <|) <$> filterMapM f xs
    Nothing -> filterMapM f xs

filterMap :: (a -> Maybe b) -> Seq a -> Seq b
filterMap f = runIdentity . filterMapM (Identity . f)

filterTraverse :: Monad m => (a -> m (Maybe b)) -> Seq a -> m (Seq b)
filterTraverse f Empty = pure Empty
filterTraverse f (x :<| xs) = do
  x' <- f x
  case x' of
    Just y -> (y <|) <$> filterTraverse f xs
    Nothing -> filterTraverse f xs

allJustOrNothing :: Seq (Maybe a) -> Maybe (Seq a)
allJustOrNothing (Just x :<| xs) = (x <|) <$> allJustOrNothing xs
allJustOrNothing (Nothing :<| _) = Nothing
allJustOrNothing Empty = Just Empty

traceWith :: (a -> String) -> a -> a
traceWith f x = trace (f x) x

tracePrettyS :: Show a => String -> a -> a
tracePrettyS s = traceWith ((s++) . shower)

tracePretty :: Show a => a -> a
tracePretty = tracePrettyS ""

appN :: Int -> (a -> a) -> (a -> a)
appN 0 _ = id
appN n f = f . appN (n - 1) f
