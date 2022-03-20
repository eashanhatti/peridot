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
  pure (testGroup "Text to STG tests"
    [ goldenVsString
        (takeBaseName konFile)
        goldenFile
        (testSurfaceToSTG <$> BL.readFile konFile)
    | konFile <- konFiles
    , let goldenFile = replaceExtension konFile ".golden" ])

testSurfaceToSTG :: BL.ByteString -> BL.ByteString
testSurfaceToSTG bs =
  case P.parse . T.decodeUtf8 . B.concat . BL.toChunks $ bs of
    Right term ->
      let
        (qs, cTerm) = elaborate' term
        ctx =
          NormContext
            (Env mempty mempty)
            mempty
            (justs (unRepUVs qs))
            (justs (unTypeUVs qs))
            (unUVEqs qs)
      in "RIGHT{" <> (fromString . shower $ (qs, stgify ctx cTerm)) <> "}"
    Left err -> "LEFT{" <> fromString err <> "}"

justs = Map.map fromJust . Map.filter isJust
