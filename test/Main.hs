module Main where

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString, findByExtension)
import System.FilePath (takeBaseName, replaceExtension)
import Data.ByteString.Lazy qualified as BL
import Data.ByteString qualified as B
import Data.Text.Encoding qualified as T
import Elaboration
import Codegen
import Syntax.Semantic
import Data.Map qualified as Map
import Normalization hiding(unTypeUVs, unUVEqs, unRepUVs)
import Elaboration.Effect
import Codegen.Stage()
import Parser qualified as P
import Data.String(fromString)
import Shower
import Data.Maybe

main :: IO ()
main = goldenTests >>= defaultMain

goldenTests :: IO TestTree
goldenTests = do
  konFiles <- findByExtension [".kon"] "."
  pure (testGroup "Text to Core tests"
    [ goldenVsString
        (takeBaseName konFile)
        goldenFile
        (testSurfaceToCore <$> BL.readFile konFile)
    | konFile <- konFiles
    , let goldenFile = replaceExtension konFile ".golden" ])

testSurfaceToCore :: BL.ByteString -> BL.ByteString
testSurfaceToCore bs =
  case P.parse . T.decodeUtf8 . B.concat . BL.toChunks $ bs of
    Right term -> fromString . shower $ elaborate' term
    Left err -> fromString err

justs = Map.map fromJust . Map.filter isJust
