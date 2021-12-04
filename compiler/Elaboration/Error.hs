module Elaboration.Error where

import qualified Norm as N
import qualified Core as C
import qualified Unification as U
import qualified Surface as S
import qualified Data.Map as Map
import Var

data InnerError
  = UnboundLocal S.Name
  | UnboundGlobal S.GName
  | UnifyError U.Error
  | TooManyParams
  | MalformedProdDec
  | ExpectedProdType
  deriving (Show, Eq)

data Error = Error N.Locals (Map.Map S.GName C.Item) Level InnerError
  deriving Eq

instance Show Error where
  show (Error ls gs lv e) = "Error\n" ++ show e ++ "\n" ++ indent "  " stringLocals ++ "\n" ++ indent "  " ("----\n" ++ stringGlobals)
    where
      indent :: String -> String -> String
      indent i s = unlines $ map (i++) (lines s)

      stringLocals = concat $ map (\l -> show l ++ "\n") ls
      stringGlobals = concat $ map (\(n, g) -> show n ++ " = " ++ show g ++ "\n") (Map.toList gs)