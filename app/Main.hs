module Main where

import qualified Core as C
import qualified Eval as E
import qualified Surface as S
import qualified Elaboration as Elab
import Parsing

prog :: S.Term
prog =
  S.Lam (S.Name "x") (S.Var $ S.Name "x")

ty :: E.Value
ty = E.FunType E.TypeType (E.Closure [] C.TypeType)

main :: IO ()
main = do
  file <- readFile "source.kon"
  case parseTerm file of
    Right term -> do
      -- putStrLn $ show term
      let (cTerm, state) = Elab.elab term E.TypeType
      putStrLn $ show cTerm
      putStrLn $ show state
    Left err -> putStrLn $ show err