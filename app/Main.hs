module Main where

import Elaboration
import Elaboration.Effect hiding(readback, eval, zonk)
import PrettyPrint hiding(unUVEqs)
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
import Data.Sequence((<|))
import Data.Bifunctor
import Numeric.Natural
import Data.Tree.View
import Search(SearchNode(..))
import "peridot" Extra

prettyError :: Map.Map Natural Natural -> Error -> Text
prettyError _ TooManyParams = "Too many parameters."
prettyError _ (UnboundVariable (UserName name)) =
  "\ESC[33mUnbound variable\ESC[0m " <> name <> "."
prettyError eqs (FailedUnify e expTy infTy) =
  "\ESC[33mMismatched types.\nExpected type\ESC[0m:\n" <>
  (indent . prettyPure eqs $ expTy) <>
  "\ESC[33mActual type\ESC[0m:\n" <>
  (indent . prettyPure eqs $ infTy) <>
  "\ESC[33mTerm\ESC[0m:\n" <>
  (indent . prettyPure eqs $ e)
prettyError eqs (ExpectedRecordType infTy) =
  "\ESC[33mExpected a record\ESC[0m.\n\ESC[33mGot a value of type\ESC[0m:\n" <>
  (indent . prettyPure eqs $ infTy)
prettyError _ (MissingField (UserName name)) =
  "\ESC[33mRecord does not have field\ESC[0m " <> name <> "."
prettyError eqs (FailedProve prop _ _) =
  "\ESC[33mFailed to prove formula\ESC[0m:\n" <>
  (indent . prettyPure eqs $ prop)
prettyError _ (AmbiguousProve prop _) =
  "\ESC[33mFormula has multiple solutions\ESC[0m."
prettyError eqs (InferredFunType infTy) =
  "\ESC[33mActual type was a function type\ESC[0m.\n" <>
  "\ESC[33mExpected type\ESC[0m:\n" <>
  (indent . prettyPure eqs $ infTy)
prettyError eqs (TooManyArgs ty) =
  "\ESC[33mIncorrect argument number\ESC[0m. \ESC[33mFunction type\ESC[0m:\n" <>
  (indent . prettyPure eqs $ ty)
prettyError _ e = pack . show $ e

prettyErrors :: Map.Map Natural Natural -> Seq (SourcePos, Error) -> Seq Text
prettyErrors eqs =
  fmap
    (\(pos, err) ->
      "Line " <>
      pack (show (unPos $ sourceLine pos)) <>
      ", column " <>
      pack (show (unPos $ sourceColumn pos)) <>
      ": " <>
      prettyError eqs err)

outputToText :: C.Term -> Maybe Text
outputToText term = pack <$> go term where
  go (C.Rigid C.TextIntroNil) = Just []
  go (C.Rigid (C.TextIntroCons c t)) = (c :) <$> go t
  go (C.TextElimCat t1 t2) = do
    t1 <- go t1
    t2 <- go t2
    Just (t1 <> t2)
  go _ = Nothing

rmGlobals = Map.mapKeys unGlobal . fmap unGlobal . fmap ((!! 0) . Set.toList)

loop = do
  prev <- newIORef []
  showSearch <- newIORef True
  let
    go :: IO ()
    go = do
      TIO.putStr "\ESC[32mPeridot\ESC[0m > "
      hFlush stdout
      input <- TIO.getLine
      let args = words input
      case args of
        [":"] -> readIORef prev >>= cmd input
        _ -> cmd input args
    cmd :: Text -> [Text] -> IO ()
    cmd input args =
      case args of
        [":set", "show_search_trees", "true"] -> writeIORef showSearch True *> go
        [":set", "show_search_trees", "false"] -> writeIORef showSearch False *> go
        [":typecheck", filename] -> do
          let sFilename = unpack filename
          r <- doesFileExist sFilename
          if r then do
            r <- elaborateFile' sFilename
            case r of
              Right (ct, qs) -> do
                let
                  tErrs =
                    prettyErrors
                      (rmGlobals (unUVEqs qs))
                      (unErrors qs)
                let tuvs = justs . unTypeUVs $ qs
                let eqs = unUVEqs qs
                let eqs' = rmGlobals eqs
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
                  flip traverse (Set.toList . Map.keysSet . unLogvarNames $ qs) \gl -> do
                    -- let !_ = tracePretty (tuvs, eqs)
                    let
                      UserName name = unLogvarNames qs ! gl
                      sol = zonk (eval (C.UniVar gl undefined)) tuvs eqs
                    case sol of
                      C.UniVar _ _ ->
                        TIO.putStrLn ("    \ESC[33mNo solution for\ESC[0m " <> name)
                      _ -> TIO.putStrLn ("    " <> name <> " = " <> prettyPure eqs' sol)
                  TIO.putStrLn ""
                  pure ()
                else
                  pure ()
                b <- readIORef showSearch
                if b && (not . null . unSearchTrees $ qs) then do
                  TIO.putStrLn "  \ESC[32mSearch Trees\ESC[0m:"
                  forM_ (unSearchTrees qs) \tree -> do
                    let
                      ttree =
                        pack .
                        showTree .
                        fmap
                          (\case
                            Atom def goal ->
                              unpack $
                              prettyPure (rmGlobals eqs) def{- <> " ||| " <>
                              prettyPure (rmGlobals eqs) goal-}
                            Fail -> "fail") $
                        tree
                    TIO.putStrLn (indent . indent $ ttree)
                else
                  pure ()
                forM_ (unOutputs qs) \(path, term) -> do
                    let text = outputToText (normalize term tuvs eqs)
                    let cTerm = readback term
                    case text of
                      Just text -> TIO.writeFile path text
                      Nothing ->
                        TIO.putStrLn
                          ("  \ESC[31mCould not output\ESC[0m\n" <>
                          (indent . indent . prettyPure eqs' $ normalize term tuvs eqs))
              Left err -> do
                TIO.putStrLn "  \ESC[31mParse error\ESC[0m:"
                putStrLn (indentS . indentS $ err)
          else
            TIO.putStrLn "  \ESC[31mFile not found.\ESC[0m"
          writeIORef prev args
          go
        [":help"] -> showCmds *> go
        [":quit"] -> do
          TIO.putStrLn "  \ESC[32mBye\ESC[0m."
          pure ()
        _ -> do
          r <- infer "REPL" input
          case r of
            Right (qs, term, ty) -> do
              let eqs' = rmGlobals (unUVEqs qs)
              let tErrs = prettyErrors eqs' (unErrors qs)
              if null tErrs then do
                TIO.putStr "  \ESC[32mInferred type\ESC[0m:\n"
                TIO.putStrLn (indent . prettyPure eqs' $ ty)
                let term' = readback . eval $ term
                TIO.putStr "  \ESC[32mEvaluated term\ESC[0m:\n"
                TIO.putStrLn (indent . prettyPure eqs' $ term')
              else do
                TIO.putStrLn "  \ESC[33mErrors\ESC[0m:"
                traverse (TIO.putStrLn . indent) tErrs
                pure ()
            Left err -> do
              TIO.putStrLn "  \ESC[31mParse error\ESC[0m:"
              putStrLn (indentS . indentS $ err)
          go
  go

showCmds = do
  TIO.putStrLn "\ESC[32mCommands\ESC[0m:"
  TIO.putStrLn "  :typecheck                    Typechecks a file"
  TIO.putStrLn "  :quit                         Quit the REPL"
  TIO.putStrLn "  :help                         Display this menu"
  TIO.putStrLn "  :set show_search_trees true   Show search trees after typechecking"
  TIO.putStrLn "  :set show_search_trees false  Don't show search trees after typechecking"

main = do
  hSetEncoding stdout utf8
  showCmds
  loop
