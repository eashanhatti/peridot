module Main where

import Elaboration
import Elaboration.Effect hiding(readback, eval)
import PrettyPrint
import Control.Monad
import Data.Text(Text, pack, words, unpack)
import Syntax.Common
import System.IO
import Data.Text.IO qualified as TIO
import Text.Megaparsec.Pos
import Prelude hiding(words)
import Data.Sequence(Seq)
import System.Directory
import System.IO

prettyError :: Error -> Text
prettyError TooManyParams = "Too many parameters."
prettyError (UnboundVariable (UserName name)) = "\ESC[33mUnbound variable\ESC[0m `" <> name <> "`."
prettyError (FailedUnify expTy infTy) =
  "\ESC[33mMismatched types.\nExpected type\ESC[0m:\n  " <>
  prettyPure expTy <>
  "\n\ESC[33mActual type\ESC[0m:\n  " <>
  prettyPure infTy
prettyError (ExpectedRecordType infTy) =
  "\ESC[33mExpected a record\ESC[0m.\n\ESC[33mGot a value of type\ESC[0m:\n  " <>
  prettyPure infTy
prettyError (MissingField (UserName name)) =
  "\ESC[33mRecord does not have field\ESC[0m `" <> name <> "`"
prettyError (FailedProve prop _ _) =
  "\ESC[33mFailed to prove formula\ESC[0m:\n  "
  <> prettyPure prop
prettyError (AmbiguousProve prop _) =
  "\ESC[33mFormula has multiple solutions\ESC[0m."
prettyError (InferredFunType infTy) =
  "\ESC[33mActual type was a function type\ESC[0m.\n" <>
  "\ESC[33mExpected type\ESC[0m:\n  " <>
  prettyPure infTy

prettyErrors :: Seq (SourcePos, Error) -> Seq Text
prettyErrors =
  fmap
    (\(pos, err) ->
      "Line " <>
      pack (show (unPos $ sourceLine pos)) <>
      ", column " <>
      pack (show (unPos $ sourceColumn pos)) <>
      ": " <>
      prettyError err)

loop = do
  TIO.putStr "\ESC[32mPeridot\ESC[0m > "
  hFlush stdout
  input <- TIO.getLine
  let args = words input
  case args of
    [":typecheck", filename] -> do
      let sFilename = unpack filename
      r <- doesFileExist sFilename
      if r then do
        r <- elaborateFile' sFilename
        case r of
          Right (_, qs) -> do
            let tErrs = prettyErrors (unErrors qs)
            if null tErrs then
              TIO.putStrLn "\ESC[32mOk\ESC[0m."
            else do
              TIO.putStrLn "\ESC[33mErrors\ESC[0m:"
              traverse TIO.putStrLn tErrs
              pure ()
          Left err -> do
            TIO.putStrLn "\ESC[31mParse error\ESC[0m:"
            putStrLn err
      else
        TIO.putStrLn "\ESC[31mFile not found.\ESC[0m"
      loop
    [":help"] -> do
      TIO.putStrLn ":typecheck    Typechecks a file"
      TIO.putStrLn ":quit         Quit the REPL"
      TIO.putStrLn ":help         Display this menu"
      loop
    [":quit"] -> do
      TIO.putStrLn "\ESC[32mBye\ESC[0m."
      pure ()
    _ -> do
      let r = infer input
      case r of
        Right (qs, term, ty) -> do
          let tErrs = prettyErrors (unErrors qs)
          if null tErrs then do
            TIO.putStr "\ESC[32mInferred type\ESC[0m:\n  "
            TIO.putStrLn (prettyPure ty)
            let term' = readback . eval $ term
            TIO.putStr "\ESC[32mEvaluated term\ESC[0m:\n  "
            TIO.putStrLn (prettyPure term')
          else do
            TIO.putStrLn "\ESC[33mErrors\ESC[0m:"
            traverse TIO.putStrLn tErrs
            pure ()
        Left err -> do
          TIO.putStrLn "\ESC[31mParse error\ESC[0m:"
          putStrLn err
      loop

main = do
  hSetEncoding stdout utf8
  TIO.putStrLn "\ESC[32mCommands\ESC[0m:"
  TIO.putStrLn ":typecheck    Typechecks a file"
  TIO.putStrLn ":quit         Quit the REPL"
  TIO.putStrLn ":help         Display this menu"
  loop