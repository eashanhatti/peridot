{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Monad.State
-- import Data.Text
-- import Data.Text.IO(putStrLn)
-- import Prelude hiding(putStrLn)
import TextShow
import TextShow.TH
import Surface
import System.Console.ANSI
import Data.Binary
import Data.Binary.Put(runPut)
import qualified Data.ByteString.Lazy as B

data Path a where
  PTop         :: Path Term
  PLamParams   :: Path Term -> [String] -> [String] -> Term -> Path String
  PLamBody     :: Path Term -> [String] -> Path Term
  PLamAddParam :: Path Term -> [String] -> Term -> Path String
  PAppTerms    :: Path Term -> [Term] -> [Term] -> Path Term
  PAppAddArg   :: Path Term -> [Term] -> Path Term
  PLetName     :: Path Term -> Term -> Term -> Term -> Path String
  PLetDefTy    :: Path Term -> String -> Term -> Term -> Path Term
  PLetDef      :: Path Term -> String -> Term -> Term -> Path Term
  PLetBody     :: Path Term -> String -> Term -> Term -> Path Term
deriving instance Show (Path a)

data PathType a where
  PTerm :: PathType Term
  PName :: PathType String

data Focus a where
  FName :: String -> Focus String
  FTerm :: Term -> Focus Term
deriving instance Show (Focus a)

unFName :: Focus String -> String
unFName (FName s) = s

unFTerm :: Focus Term -> Term
unFTerm (FTerm e) = e

data FocusType a where
  FTName :: FocusType String
  FTTerm :: FocusType Term

data Cursor a = Cursor { unFocus :: Focus a, unPath :: Path a }
deriving instance Show (Cursor a)

data EditorState a = EditorState { unCursor :: Cursor a, unFocusType :: FocusType a }

data Ex = forall a. Ex { unEx :: EditorState a }

data Command a where
  InsertLam  :: String -> Command Term
  InsertApp  :: Command Term
  InsertVar  :: String -> Command Term
  InsertHole :: Command Term
  InsertLet  :: Command Term
  SetName    :: String -> Command String
  MoveOut    :: Command a
  MoveRight  :: Command a
  MoveLeft   :: Command a
  MoveIn     :: Command a

run :: Command a -> EditorState a -> Ex
run command state@(EditorState (Cursor focus path) _) = case command of
  InsertLam n -> Ex $ EditorState (Cursor (FName "") (PLamAddParam path [n] Hole)) FTName
  InsertApp -> Ex $ EditorState (Cursor (FTerm Hole) (PAppTerms path [] [Hole])) FTTerm
  InsertVar s -> Ex $ EditorState (Cursor (FTerm $ Var (Name s)) path) FTTerm
  InsertHole -> Ex $ EditorState (Cursor (FTerm Hole) path) FTTerm
  InsertLet -> Ex $ EditorState (Cursor (FName "") (PLetName path Hole Hole Hole)) FTName
  SetName s -> Ex $ EditorState (Cursor (FName s) path) FTName
  MoveRight -> case path of
    PTop -> Ex state
    PLamParams up ln [] body -> Ex $ EditorState (Cursor (FName "") (PLamAddParam up (ln ++ [unFName focus]) body)) FTName
    PLamParams up ln rs body -> Ex $ EditorState (Cursor (FName $ last rs) (PLamParams up (ln ++ [unFName focus]) (init rs) body)) FTName
    PLamAddParam up ns body ->
      if unFName focus == "" then
        Ex $ EditorState (Cursor (FTerm body) (PLamBody up ns)) FTTerm
      else
        Ex $ EditorState (Cursor (FName "") (PLamAddParam up (ns ++ [unFName focus]) body)) FTName
    PLamBody up ns -> run MoveOut state
    PAppTerms up le [] -> Ex $ EditorState (Cursor (FTerm EditorBlank) (PAppAddArg up (le ++ [unFTerm focus]))) FTTerm
    PAppTerms up le re -> Ex $ EditorState (Cursor (FTerm $ last re) (PAppTerms up (le ++ [unFTerm focus]) (init re))) FTTerm
    PAppAddArg up es ->
      if unFTerm focus == EditorBlank then
        run MoveOut state
      else
        Ex $ EditorState (Cursor (FTerm EditorBlank) (PAppAddArg up (es ++ [unFTerm focus]))) FTTerm
    PLetName up def defTy body -> Ex $ EditorState (Cursor (FTerm defTy) (PLetDefTy up (unFName focus) def body)) FTTerm
    PLetDefTy up name def body -> Ex $ EditorState (Cursor (FTerm def) (PLetDef up name (unFTerm focus) body)) FTTerm
    PLetDef up name defTy body -> Ex $ EditorState (Cursor (FTerm body) (PLetBody up name (unFTerm focus) defTy)) FTTerm
    PLetBody _ _ _ _ -> run MoveOut state
  MoveLeft -> case path of
    PTop -> Ex state
    PLamParams up [] rn body -> run MoveOut state
    PLamParams up ln rn body -> Ex $ EditorState (Cursor (FName (last ln)) (PLamParams up (init ln) ((unFName focus):rn) body)) FTName
    PLamAddParam up ns body ->
      if unFName focus == "" then
        Ex $ EditorState (Cursor (FName (last ns)) (PLamParams up (init ns) [] body)) FTName
      else
        Ex $ EditorState (Cursor (FName (last ns)) (PLamParams up (init ns) [(unFName focus)] body)) FTName
    PLamBody up ns -> Ex $ EditorState (Cursor (FName "") (PLamAddParam up ns (unFTerm focus))) FTName
    PAppTerms up [] re -> run MoveOut state
    PAppTerms up le re -> Ex $ EditorState (Cursor (FTerm $ last le) (PAppTerms up (init le) ((unFTerm focus):re))) FTTerm
    PAppAddArg up es ->
      let re = if unFTerm focus == EditorBlank then [] else [unFTerm focus]
      in Ex $ EditorState (Cursor (FTerm $ last es) (PAppTerms up (init es) re)) FTTerm
    PLetName _ _ _ _ -> run MoveOut state
    PLetDefTy up name def body -> Ex $ EditorState (Cursor (FName name) (PLetName up def (unFTerm focus) body)) FTName
    PLetDef up name defTy body -> Ex $ EditorState (Cursor (FTerm defTy) (PLetDefTy up name (unFTerm focus) body)) FTTerm
    PLetBody up name def defTy -> Ex $ EditorState (Cursor (FTerm def) (PLetDef up name defTy (unFTerm focus))) FTTerm
  MoveOut -> case path of
    PTop -> Ex state
    PLamParams up ln rn body -> Ex $ EditorState (Cursor (FTerm (Lam (map Name ln ++ [Name $ unFName focus] ++ map Name rn) body)) up) FTTerm
    PLamBody up ns -> Ex $ EditorState (Cursor (FTerm $ Lam (map Name ns) (unFTerm focus)) up) FTTerm
    PLamAddParam up ns body -> Ex $ EditorState (Cursor (FTerm $ Lam (map Name ns ++ [Name $ unFName focus]) body) up) FTTerm
    PAppTerms up le re -> let es = le ++ [unFTerm focus] ++ re in Ex $ EditorState (Cursor (FTerm $ App (head es) (tail es)) up) FTTerm
    PAppAddArg up es ->
      let es' = if unFTerm focus == EditorBlank then es else es ++ [unFTerm focus]
      in Ex $ EditorState (Cursor (FTerm $ App (head es') (tail es')) up) FTTerm
    PLetName up def defTy body -> Ex $ EditorState (Cursor (FTerm $ Let (Name $ unFName focus) def defTy body) up) FTTerm
    PLetDefTy up name def body -> Ex $ EditorState (Cursor (FTerm $ Let (Name name) def (unFTerm focus) body) up) FTTerm
    PLetDef up name defTy body -> Ex $ EditorState (Cursor (FTerm $ Let (Name name) (unFTerm focus) defTy body) up) FTTerm
    PLetBody up name def defTy -> Ex $ EditorState (Cursor (FTerm $ Let (Name name) def defTy (unFTerm focus)) up) FTTerm
  MoveIn -> case focus of
    FTerm focus -> case focus of
      Lam ns body -> Ex $ EditorState (Cursor (FTerm body) (PLamBody path (map unName ns))) FTTerm
      Var _ -> Ex state
      App lam args -> Ex $ EditorState (Cursor (FTerm lam) (PAppTerms path [] args)) FTTerm
      Let (Name name) def defTy body -> Ex $ EditorState (Cursor (FTerm body) (PLetBody path name def defTy)) FTTerm
    FName _ -> Ex state

-- toBinary :: Term -> Put
-- toBinary term = do

-- export :: EditorState a -> String -> IO ()
-- export (EditorState cursor _) fn = do
--   let (FTerm program) = loop cursor
--   let bs = runPut $ toBinary program
--   B.writeFile fn bs
--   where
--     loop :: Cursor a -> Focus Term
--     loop (Cursor focus path) = case path of
--       PTop -> focus
--       PLamParams up ls rs body -> loop $ Cursor (FTerm $ Lam (map Name ls ++ [Name $ unFName focus] ++ map Name rs) body) up
--       PLamBody up ns -> loop $ Cursor (FTerm $ Lam (map Name ns) (unFTerm focus)) up
--       PLamAddParam up ns body -> loop $ Cursor (FTerm $ Lam (map Name ns) body) up

render :: EditorState a -> String
render (EditorState (Cursor focus path) _) = renderPath ("[" ++ renderFocus focus ++ "]") (simpleFocus focus) path where
  renderFocus :: Focus a -> String
  renderFocus focus = case focus of
    FName s -> s
    FTerm term -> renderTerm term
  renderTerm :: Term -> String
  renderTerm term = case term of
    Lam names body -> "\\" ++ snames (map unName names) ++ ". " ++ renderTerm body
    App lam args ->
      let se = if simple lam then renderTerm lam else "(" ++ renderTerm lam ++ ")"
      in se ++ space args ++ sterms args
    Var (Name s) -> s
    Hole -> "?"
    Let (Name name) def defTy body -> "let " ++ name ++ " : " ++ renderTerm defTy ++ " = " ++ renderTerm def ++ " in\n" ++ renderTerm body
    EditorBlank -> "_"
  renderPath :: String -> Bool -> Path a -> String
  renderPath focus isSimple path = case path of
    PTop -> focus
    PLamBody up names -> renderPath ("\\" ++ snames names ++ ". " ++ focus) False up
    PLamParams up ln rn body -> renderPath ("\\" ++ snames ln ++ focus ++ snames rn ++ ". " ++ renderTerm body) False up
    PLamAddParam up ns body -> renderPath ("\\" ++ snames ns ++ focus ++ ". " ++ renderTerm body) False up
    PAppTerms up le re -> renderPath (sterms le ++ space le ++ parenFocus isSimple focus ++ space re ++ sterms re) False up
    PAppAddArg up args -> renderPath (sterms args ++ space args ++ parenFocus isSimple focus) False up
    PLetName up def defTy body ->
      renderPath ("let " ++ focus ++ " : " ++ renderTerm defTy ++ " = " ++ renderTerm def ++ " in\n" ++ renderTerm body) False up
    PLetDef up name defTy body ->
      renderPath ("let " ++ name ++ " : " ++ renderTerm defTy ++ " = " ++ focus ++ " in\n" ++ renderTerm body) False up
    PLetDefTy up name def body ->
      renderPath ("let " ++ name ++ " : " ++ focus ++ " = " ++ renderTerm def ++ " in\n" ++ renderTerm body) False up
    PLetBody up name def defTy ->
      renderPath ("let " ++ name ++ " : " ++ renderTerm defTy ++ " = " ++ renderTerm def ++ " in\n" ++ focus) False up
  parenFocus isSimple focus = if isSimple then focus else "(" ++ focus ++ ")"
  
  simpleFocus :: Focus a -> Bool
  simpleFocus focus = case focus of
    FName _ -> True
    FTerm term -> simple term
  
  simple term = case term of
    Var _ -> True
    Hole -> True
    _ -> False
  space xs = case xs of
    [] -> ""
    _ -> " "
  sterms es = case es of
    [] -> ""
    e:es ->
      let se = if simple e then renderTerm e else "(" ++ renderTerm e ++ ")"
      in se ++ space es ++ sterms es
  snames ns = case ns of
    [] -> ""
    n:ns -> n ++ " " ++ snames ns

loop :: EditorState a -> IO ()
loop state = do
  clearScreen
  putStrLn (show $ unCursor state)
  putStrLn (render state)
  s <- getLine
  state <- case (s, unFocusType state) of
    -- ("e", _) -> do
    --   fn <- getLine
    --   export state fn
    --   pure $ Ex state
    ("r", _) -> pure $ run MoveRight state
    ("l", _) -> pure $ run MoveLeft state
    ("o", _) -> pure $ run MoveOut state
    ("i", _) -> pure $ run MoveIn state
    ("d", FTTerm) -> pure $ run InsertHole state
    ("lam", FTTerm) -> do
      n <- getLine
      pure $ run (InsertLam n) state
    ("let", FTTerm) -> pure $ run InsertLet state
    ("app", FTTerm) -> pure $ run InsertApp state
    (_, FTTerm) -> pure $ run (InsertVar s) state
    (_, FTName) -> pure $ run (SetName s) state
  next state
  where
    next :: Ex -> IO ()
    next (Ex state) = loop state

main :: IO ()
main = loop (EditorState (Cursor (FTerm Hole) PTop) FTTerm)