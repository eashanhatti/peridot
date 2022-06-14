module Main where

import Elaboration
import Elaboration.Effect
import PrettyPrint
import Control.Monad
import Data.Text(Text, pack)
import Syntax.Common
import System.IO
import Data.Text.IO qualified as TIO
import Text.Megaparsec.Pos

prettyError :: Error -> Text
prettyError (UnboundVariable (UserName name)) = "\ESC[33mUnbound variable\ESC[0m `" <> name <> "`"
prettyError (FailedUnify expTy infTy) =
  "\ESC[33mMismatched types\nExpected type\ESC[0m:\n  " <>
  prettyPure expTy <>
  "\n\ESC[33mActual type\ESC[0m:\n  " <>
  prettyPure infTy

loop = do
  TIO.putStr "\ESC[32mPeridot\ESC[0m > "
  hFlush stdout
  args <- words <$> getLine
  case args of
    [":typecheck", filename] -> do
      r <- elaborateFile' filename
      case r of
        Right (_, qs) -> do
          let
            tErrs =
                fmap
                  (\(pos, err) ->
                    "Line " <>
                    pack (show (unPos $ sourceLine pos)) <>
                    ", column " <>
                    pack (show (unPos $ sourceColumn pos)) <>
                    ": " <>
                    prettyError err)
                  (unErrors qs)
          if null tErrs then
            TIO.putStrLn "\ESC[32mOk\ESC[0m."
          else do
            TIO.putStrLn "\ESC[33mErrors\ESC[0m."
            traverse TIO.putStrLn tErrs
            pure ()
        Left err -> do
          TIO.putStrLn "\ESC[31mParse error\ESC[0m."
          putStrLn err
      loop
    [":help"] -> do
      TIO.putStrLn "`:typecheck`    Typechecks a file"
      TIO.putStrLn "`:quit`         Quit the REPL"
      TIO.putStrLn "`:help`         Display this menu"
      loop
    [":quit"] -> do
      TIO.putStrLn "\ESC[32mBye\ESC[0m."
      pure ()
    _ -> do
      TIO.putStrLn ("\ESC[31mInvalid command\ESC[0m.")
      loop

main = do
  TIO.putStrLn "\ESC[32mCommands\ESC[0m."
  TIO.putStrLn ":typecheck    Typechecks a file"
  TIO.putStrLn ":quit         Quit the REPL"
  TIO.putStrLn ":help         Display this menu"
  loop