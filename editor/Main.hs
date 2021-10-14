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

data Path a where
  PTop          :: Path a
  PLamParamList :: Path b -> [String] -> [String] -> Term -> Path String
  PLamBody      :: Path b -> [String] -> Path Term
  PLamAddParam  :: Path b -> [String] -> Term -> Path String
  PApp          :: Path b -> [Term] -> [Term] -> Path Term
deriving instance Show (Path a)

data Focus a where
  FName :: String -> Focus String
  FTerm   :: Term -> Focus Term
deriving instance Show (Focus a)

unFName :: Focus String -> String
unFName (FName s) = s

data FocusType a where
  FTName :: FocusType String
  FTTerm   :: FocusType Term

data Cursor a = Cursor { unFocus :: Focus a, unPath :: Path a }
deriving instance Show (Cursor a)

data EditorState a = EditorState { unCursor :: Cursor a, unFocusType :: FocusType a }

data Ex = forall a. Ex (EditorState a)

data Command a where
  InsertLam :: Command Term
  InsertApp :: Command Term
  InsertVar :: Command Term
  SetName   :: String -> Command String
  MoveOut   :: Command a
  MoveRight :: Command a
  MoveLeft  :: Command a
  MoveIn    :: Command a
  Add       :: Command a

run :: Command a -> EditorState a -> Ex
run command state@(EditorState (Cursor focus path) _) = case command of
  InsertLam -> Ex $ EditorState (Cursor (FName "") (PLamParamList path [] [] Hole)) FTName
  SetName s -> EditorState (Cursor (FName s) path) FTName
  MoveRight -> case path of
    PTop -> Ex $ state
    PLamParamList up ln (r:rn) body -> Ex $ EditorState (Cursor (FName r) (PLamParamList up ((unFName focus):ln) rn body)) FTName
    PLamParamList up ln [] body -> Ex $ EditorState (Cursor (FName "") (PLamAddParam up ((unFName focus):ln) body)) FTName
    PLamAddParam up ns body ->
      if unFName focus == "" then
        Ex $ EditorState (Cursor (FTerm body) (PLamBody up ns)) FTTerm
      else
        Ex $ EditorState (Cursor (FName "") (PLamAddParam up (ns ++ [unFName focus]) body)) FTName

render :: EditorState a -> String
render (EditorState (Cursor focus path) _) = renderPath ("[" ++ renderFocus focus ++ "]") path where
  renderFocus :: Focus a -> String
  renderFocus focus = case focus of
    FName s -> s
    FTerm term -> renderTerm term
  renderTerm :: Term -> String
  renderTerm term = case term of
    Lam names body -> "\\" ++ snames (map (\(Name n) -> n) names) ++ ". " ++ renderTerm body where
    Hole -> "?"
  renderPath :: String -> Path a -> String
  renderPath focus path = case path of
    PTop -> focus
    PLamBody up names -> renderPath ("\\" ++ snames names ++ ". " ++ focus) up where
    PLamParamList up ln rn body -> renderPath ("\\" ++ snames ln ++ focus ++ snames rn ++ ". " ++ renderTerm body) up
    PLamAddParam up ns body -> renderPath ("\\" ++ snames ns ++ focus ++ ". " ++ renderTerm body) up
  snames ns = case ns of
    [] -> ""
    n:ns -> n ++ " " ++ snames ns

loop :: EditorState a -> IO ()
loop state = do
  putStrLn (render state)
  s <- getLine
  state <- pure $ case (s, unFocusType state) of
    ("\\right", _) -> run MoveRight state
    ("lam", FTTerm) -> run InsertLam state
    (_, FTName) -> run (SetName s) state
  next state
  where
    next :: Ex -> IO ()
    next (Ex state) = loop state

main :: IO ()
main = loop (EditorState (Cursor (FTerm Hole) PTop) FTTerm)