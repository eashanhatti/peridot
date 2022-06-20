module Main where

import Elaboration
import Elaboration.Effect hiding(readback, eval, zonk)
import PrettyPrint
import Control.Monad
import Parser qualified as P
import Data.Text(Text, pack, words, unpack, lines, unlines)
import Syntax.Common
import Syntax.Surface
import System.IO
import Syntax.Core qualified as C
import Data.Text.IO qualified as TIO
import Text.Megaparsec.Pos
import Prelude hiding(words, lines, unlines)
import Prelude qualified as P
import Data.Sequence(Seq)
import System.Directory
import System.IO
import Data.IORef
import Data.Map qualified as Map
import Data.Set qualified as Set
import "peridot" Extra
import Data.Sequence((<|))

indentS = P.unlines . fmap ("  "<>) . P.lines
indent = unlines . fmap ("  "<>) . lines

prettyError :: Error -> Text
prettyError TooManyParams = "Too many parameters."
prettyError (UnboundVariable (UserName name)) = "\ESC[33mUnbound variable\ESC[0m `" <> name <> "`."
prettyError (FailedUnify expTy infTy) =
  "\ESC[33mMismatched types.\nExpected type\ESC[0m:\n" <>
  (indent . prettyPure $ expTy) <>
  "\n\ESC[33mActual type\ESC[0m:\n" <>
  (indent . prettyPure $ infTy)
prettyError (ExpectedRecordType infTy) =
  "\ESC[33mExpected a record\ESC[0m.\n\ESC[33mGot a value of type\ESC[0m:\n" <>
  (indent . prettyPure $ infTy)
prettyError (MissingField (UserName name)) =
  "\ESC[33mRecord does not have field\ESC[0m `" <> name <> "`"
prettyError (FailedProve prop _ _) =
  "\ESC[33mFailed to prove formula\ESC[0m:\n" <>
  (indent . prettyPure $ prop)
prettyError (AmbiguousProve prop _) =
  "\ESC[33mFormula has multiple solutions\ESC[0m."
prettyError (InferredFunType infTy) =
  "\ESC[33mActual type was a function type\ESC[0m.\n" <>
  "\ESC[33mExpected type\ESC[0m:\n" <>
  (indent . prettyPure $ infTy)
prettyError e = pack . show $ e

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

outputToText :: C.Term -> Maybe Text
outputToText term = pack <$> go term where
  go (C.Rigid C.TextIntroNil) = Just []
  go (C.Rigid (C.TextIntroCons c t)) = (c :) <$> go t
  go (C.TextElimCat t1 t2) = do
    t1 <- go t1
    t2 <- go t2
    Just (t1 <> t2)
  go _ = Nothing

loop = do
  prev <- newIORef []
  let
    go :: IO ()
    go = do
      TIO.putStr "\ESC[34mPeridot\ESC[0m > "
      hFlush stdout
      input <- TIO.getLine
      let args = words input
      case args of
        [":"] -> readIORef prev >>= cmd input
        _ -> cmd input args
    cmd :: Text -> [Text] -> IO ()
    cmd input args =
      case args of
        [":typecheck", filename] -> do
          let sFilename = unpack filename
          r <- doesFileExist sFilename
          if r then do
            r <- elaborateFile' sFilename
            case r of
              Right (_, qs) -> do
                let tErrs = prettyErrors (unErrors qs)
                let tuvs = justs . unTypeUVs $ qs
                let
                  sols =
                    Map.filterWithKey
                      (\k _ -> case k of
                        UVGlobal gl -> gl < 1000
                        _ -> False)
                      (unTypeUVs qs)
                if null tErrs then do
                  TIO.putStrLn "  \ESC[32mOk\ESC[0m.\n"
                else do
                  TIO.putStrLn "  \ESC[33mErrors\ESC[0m:"
                  traverse (TIO.putStrLn . indent) tErrs
                  pure ()
                if not . null . unLogvarNames $ qs then do
                  TIO.putStrLn "  \ESC[32mSolutions\ESC[0m:"
                  flip traverse (Set.toList . Map.keysSet . unLogvarNames $ qs) \gl ->
                    let
                      UserName name = unLogvarNames qs ! gl
                      sol = Map.lookup gl tuvs
                    in
                      case sol of
                        Just sol -> do
                          let cSol = zonk sol tuvs
                          TIO.putStrLn ("    " <> name <> " = " <> prettyPure cSol)
                        Nothing -> TIO.putStrLn ("    \ESC[33mNo solution for\ESC[0m " <> name)
                  TIO.putStrLn ""
                  pure ()
                else
                  pure ()
                forM_ (unOutputs qs) \(path, term) -> do
                    let text = outputToText (normalize term tuvs)
                    let cTerm = readback term
                    case text of
                      Just text -> TIO.writeFile path text
                      Nothing ->
                        TIO.putStrLn
                          ("  \ESC[31mCould not output\ESC[0m\n" <>
                          (indent . indent . prettyPure . normalize term $ tuvs))
              Left err -> do
                TIO.putStrLn "  \ESC[31mParse error\ESC[0m:"
                putStrLn (indentS err)
          else
            TIO.putStrLn "  \ESC[31mFile not found.\ESC[0m"
          writeIORef prev args
          go
        [":help"] -> do
          TIO.putStrLn "  :typecheck    Typechecks a file"
          TIO.putStrLn "  :quit         Quit the REPL"
          TIO.putStrLn "  :help         Display this menu"
          go
        [":quit"] -> do
          TIO.putStrLn "  \ESC[32mBye\ESC[0m."
          pure ()
        _ -> do
          let r = infer input
          case r of
            Right (qs, term, ty) -> do
              let tErrs = prettyErrors (unErrors qs)
              if null tErrs then do
                TIO.putStr "  \ESC[32mInferred type\ESC[0m:\n"
                TIO.putStrLn (indent . prettyPure $ ty)
                let term' = readback . eval $ term
                TIO.putStr "  \ESC[32mEvaluated term\ESC[0m:\n"
                TIO.putStrLn (indent . prettyPure $ term')
              else do
                TIO.putStrLn "  \ESC[33mErrors\ESC[0m:"
                traverse (TIO.putStrLn . indent) tErrs
                pure ()
            Left err -> do
              TIO.putStrLn "  \ESC[31mParse error\ESC[0m:"
              putStrLn (indentS err)
          go
  go

main = do
  hSetEncoding stdout utf8
  TIO.putStrLn "\ESC[32mCommands\ESC[0m:"
  TIO.putStrLn "  :typecheck    Typechecks a file"
  TIO.putStrLn "  :quit         Quit the REPL"
  TIO.putStrLn "  :help         Display this menu"
  loop