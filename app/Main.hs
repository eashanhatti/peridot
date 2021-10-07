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
import Text.Pretty.Simple(pShow)
import qualified Data.Text.Lazy.IO as Text

-- e = C.Letrec [C.Var (Index 0) C.TypeType0] (C.Var (Index 1) C.ElabError)
-- e = C.Letrec [C.TypeType1] (C.Var (Index 0) C.ElabError)
-- e = C.Letrec [] C.TypeType1

-- main :: IO ()
-- main = do
--   putStrLn $ show $ runReader (N.eval e) (Level 0, mempty, [])

main :: IO ()
main = do
  file <- readFile "source.kon"
  putStrLn "Start parsing"
  let tokens = Parse.lex file
  putStrLn $ show tokens
  let program = Parse.parseTerm tokens
  putStrLn "Done parsing"
  putStrLn "Surface term:"
  Text.putStrLn $ pShow program
  let (cProgram, state) = Elab.elab program
  putStrLn "Core program:"
  Text.putStrLn $ pShow cProgram
  putStrLn "Errors:"
  forM_ (Elab.errors state) (putStrLn . show)
  putStrLn "Metas:"
  forM_ (toList $ Elab.metas state) (putStrLn . show)
  -- if length (Elab.errors state) == 0 then do
  --   putStrLn "After partial eval:"
  --   let resiTerm = PE.partialEval cTerm
  --   putStrLn $ show $ resiTerm
  -- else
  --   pure ()