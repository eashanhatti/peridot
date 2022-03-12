module Main where

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString, findByExtension)
import System.FilePath (takeBaseName, replaceExtension)
import Data.ByteString.Lazy qualified as BL
import Data.ByteString qualified as B
import Data.Text.Encoding qualified as T
import Elaboration
import Codegen.Stage qualified as CS
import Codegen.Lower qualified as CL
import Parser qualified as P
import Data.String(fromString)
import Shower
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
    Right term -> "RIGHT{" <> (fromString . shower $ elaborate' term) <> "}"
    Left err -> "LEFT{" <> fromString err <> "}"
