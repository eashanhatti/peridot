module Main where

import Test.Tasty(defaultMain, TestTree, testGroup)
import Test.Tasty.Golden(goldenVsString, findByExtension)
import System.FilePath
import Data.ByteString.Lazy qualified as BL
import Data.ByteString qualified as B
import Data.Text.Encoding qualified as T
import Elaboration
import Syntax.Semantic
import Data.Map qualified as Map
import Normalization hiding(unTypeUVs, unUVEqs, unRepUVs)
import Elaboration.Effect
import Parser qualified as P
import Data.String(fromString)
import Shower
import Data.Maybe
import Syntax.Surface qualified as S

main :: IO ()
main = goldenTests >>= defaultMain

goldenTests :: IO TestTree
goldenTests = do
  konFiles <- findByExtension [".per"] "test/"
  pure (testGroup "Text to Core tests"
    [ goldenVsString
        (takeBaseName konFile)
        goldenFile
        (do
          bs <- BL.readFile konFile
          let t = T.decodeUtf8 . B.concat . BL.toChunks $ bs
          r <- P.parse P.toplevel konFile t
          case r of
            Right term -> fromString . shower <$> elaborate' term
            Left err -> pure (fromString err))
    | konFile <- konFiles
    , let
        goldenFile =
          dropFileName konFile </>
          "golden_files" </>
          takeFileName (replaceExtension konFile ".golden") ])

justs = Map.map fromJust . Map.filter isJust
