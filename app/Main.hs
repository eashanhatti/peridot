module Main where

import qualified Core as C
import qualified Eval as E
import qualified Surface as S
import qualified Elaboration as Elab
import Parsing
import Control.Monad(forM_)
import Data.Map(toList)

prog :: S.Term
prog =
  S.Lam (S.Name "x") (S.Var $ S.Name "x")

ty :: E.Value
ty = E.FunType E.TypeType (E.Closure [] C.TypeType)

main :: IO ()
main = do
  file <- readFile "source.kon"
  let t = parseTerm file
  putStrLn "Done parsing"
  case t of
    Right term -> do
      -- putStrLn "Surface term:"
      -- putStrLn $ show term
      let (cTerm, state) = Elab.elab term E.TypeType
      putStrLn "Core term:"
      putStrLn $ show cTerm
      putStrLn "Errors:"
      forM_ (Elab.errors state) (putStrLn . show)
      putStrLn "Metas:"
      forM_ (toList $ Elab.metas state) (putStrLn . show)
    Left err -> putStrLn $ show err