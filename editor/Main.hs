{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad.State
-- import Data.Text
-- import Data.Text.IO(putStrLn)
-- import Prelude hiding(putStrLn)
import TextShow
import TextShow.TH

data Ast
  = Lam [Ast] Ast
  | App Ast [Ast]
  | Var String
  | Name String
  | Hole
  deriving Show
-- $(deriveTextShow ''Ast)

data Context
  = CTop
  | CLam Context [Ast] [Ast] (Maybe Ast)
  | CApp Context [Ast] [Ast]
  deriving Show
-- $(deriveTextShow ''Context)

data Cursor = Cursor { unFocus :: Ast, unContext :: Context }
  deriving Show
-- $(deriveTextShow ''Cursor)

data EditorState = EditorState { unCursor :: Cursor }

type Edit = State EditorState ()

data Prompt = PLam | PApp | PVar | PUp | PRight | PLeft | PDown

putFocus :: Ast -> Edit
putFocus focus = do
  context <- unContext <$> unCursor <$> get
  put $ EditorState (Cursor focus context)

putContext :: Context -> Edit
putContext context = do
  focus <- unFocus <$> unCursor <$> get
  put $ EditorState (Cursor focus context)

putCursor :: Ast -> Context -> Edit
putCursor focus context = putFocus focus >> putContext context

run :: Prompt -> Edit
run prompt = do
  (Cursor focus context) <- unCursor <$> get
  case prompt of
    PLam -> putFocus (Lam [] Hole)
    PDown -> case focus of
      Lam ns b -> putCursor b (CLam context [Name "_"] [] Nothing)

render :: EditorState -> String
render (EditorState cursor) = show cursor

loop :: EditorState -> IO ()
loop state = do
  putStrLn $ render state
  s <- getLine
  prompt <- pure $ case s of
    "lam" -> PLam
    "d" -> PDown
  let state' = execState (run prompt) state
  loop state'

main :: IO ()
main = loop $ EditorState (Cursor Hole CTop)