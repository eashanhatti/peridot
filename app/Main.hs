{-# LANGUAGE ScopedTypeVariables #-} 

module Main where

import qualified Core as C
import qualified Norm as N
import qualified Surface as S
import qualified Elaboration as Elab
import qualified Parsing as Parse
import qualified PartialEval as PE
import Control.Monad(forM_)
import Data.Map(toList)
import Data.Either(fromRight)

prog :: S.Term
prog =
  S.Lam (S.Name "x") (S.Var $ S.Name "x")

ty :: N.Value
ty = N.FunType N.TypeType (N.Closure [] C.TypeType)

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
  let (cTerm, state) = Elab.elab term N.TypeType
  putStrLn "Core term:"
  putStrLn $ show cTerm
  putStrLn "After partial eval:"
  let resiTerm = PE.partialEval cTerm
  putStrLn $ show $ resiTerm
  putStrLn "Errors:"
  forM_ (Elab.errors state) (putStrLn . show)
  putStrLn "Metas:"
  forM_ (toList $ Elab.metas state) (putStrLn . show)
  forM_ (toList $ Elab.stageMetas state) (putStrLn . show)
  -- if length (Elab.errors state) == 0 then do
  -- else
  --   pure ()