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
  let term = Parse.parseTerm tokens
  putStrLn "Done parsing"
  putStrLn "Surface term:"
  putStrLn $ show term
  let (cTerm, state) = Elab.elab term (N.QuoteType N.TypeType0)
  putStrLn "Core term:"
  putStrLn $ show cTerm
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