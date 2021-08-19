module Main where

import qualified Core as C
import qualified Eval as E
import qualified Surface as S
import qualified Elaboration as Elab

prog :: S.Term
prog =
  S.Lam (S.Name "x") (S.Var $ S.Name "x")

ty :: E.Value
ty = E.FunType E.TypeType (E.Closure [] C.TypeType)

main :: IO ()
main = putStrLn $ show $ fst $ Elab.elab prog ty