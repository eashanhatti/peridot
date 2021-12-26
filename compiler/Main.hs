{-# LANGUAGE PatternSynonyms #-}

module Main where

import qualified Core as C
import qualified Norm as N
import qualified Surface as S
import Surface(Item(..), Name, pattern Name, Term(..), Constructor, pattern Constructor, GName, pattern GName, Pattern(..), pattern Clause)
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

-- e :: S.Item
-- e = S.NamespaceDef (S.Name "main") [
--     S.IndDef (S.Name "Unit") S.U1 [
--       S.Constructor (S.Name "unit") (S.GVar (S.GName ["Unit", "main"]))
--     ],
--     S.TermDef
--       (S.Name "foo")
--       (S.Pi (S.Name "_") (S.GVar (S.GName ["Unit", "main"])) (S.GVar (S.GName ["Unit", "main"])))
--       (S.Match [
--         S.Clause
--           (S.AppPat [S.ConPat (S.GName ["unit", "Unit", "main"]) []])
--           (S.GVar (S.GName ["unit", "Unit", "main"]))
--       ])
--   ]

bool = GVar (GName ["Bool", "main"])
true = GVar (GName ["true", "Bool", "main"])
trueP = ConPat (GName ["true", "Bool", "main"]) []
falseP = ConPat (GName ["false", "Bool", "main"]) []
isTrueP = ConPat (GName ["is_true", "IsTrue", "main"]) []
isTrue = GVar (GName ["IsTrue", "main"])

e :: Item
e = NamespaceDef (Name "main") [
    IndDef (Name "Bool") U1 [
      Constructor (Name "true") bool,
      Constructor (Name "false") bool
    ],
    IndDef (Name "IsTrue") (Pi (Name "_") bool U1) [
      Constructor (Name "is_true") (App isTrue [true])
    ],
    TermDef (Name "example")
      (Pi (Name "b") bool $ Pi (Name "_") (App isTrue [Var (Name "b")]) $ bool)
      (Match [
        Clause (AppPat [falseP, isTrueP]) true
      ])
  ]

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