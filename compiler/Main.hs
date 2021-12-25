module Main where

import qualified Core as C
import qualified Norm as N
import qualified Surface as S
import Var
import qualified Elaboration as Elab
import qualified Parsing as Parse
-- import qualified PartialEval as PE
import Control.Monad(forM_)
import Control.Monad.Reader(runReader)
import Data.Map(toList)
import Data.Either(fromRight)
-- import Text.Pretty.Simple(pShow)
import qualified Data.Text.Lazy.IO as Text
import Data.Binary.Get(runGet)
import Data.ByteString.Lazy(readFile)
import Prelude hiding(readFile)

-- main :: IO ()
-- main = do
--   putStrLn $ show $ runReader (N.eval e) (Level 0, mempty, [])

e :: S.Item
e = undefined

main :: IO ()
main = do
  file <- readFile "source.kon"
  putStrLn "Start parsing"
  let program = e
  putStrLn "Done parsing"
  putStrLn "Surface term:"
  -- Text.putStrLn $ pShow program
  putStrLn $ show program
  let (cProgram, state) = Elab.elabFresh program
  putStrLn "Core program:"
  -- Text.putStrLn $ pShow cProgram
  putStrLn $ show cProgram
  putStrLn "Errors:"
  forM_ (Elab.errors state) (putStrLn . show)
  putStrLn "Metas:"
  forM_ (toList $ Elab.metas state) (putStrLn . show)