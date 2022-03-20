module Extra where

import Data.Map qualified as Map
import Shower
import Data.Maybe

fromRight :: Either () a -> a
fromRight (Right x) = x

(!) :: (Ord k, Show k, Show v) => Map.Map k v -> k -> v
(!) m k = case Map.lookup k m of
  Just v -> v
  Nothing -> error $ "MAP LOOKUP: " ++ shower (k, m)

justs = Map.map fromJust . Map.filter isJust
