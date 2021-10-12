module Main where

data Ast = Item String | Node [Ast] | Pos
  deriving Show

showAst :: String -> Ast -> String
showAst indent ast = case ast of
  Item s -> indent ++ s
  Node ns -> indent ++ "tree" ++ show (length ns) ++ go ns where
    go ns = case ns of
      [] -> ""
      n:ns -> "\n" ++ showAst (indent ++ "  ") n ++ go ns
  Pos -> indent ++ "@"

data Path
  = Top
  | Point Path [Ast] [Ast] -- up, left, right
  deriving Show

data Cursor = Cursor Ast Path -- focus, context
  deriving Show

render :: Cursor -> String
render cursor = let (Cursor ast _) = focusTop cursor in showAst "" ast

focusTop :: Cursor -> Cursor
focusTop cursor@(Cursor _ path) = case path of
  Top -> cursor
  Point _ _ _ -> focusTop $ focusUp cursor

focusLeft :: Cursor -> Cursor
focusLeft cursor@(Cursor focus path) = case path of
  Top -> cursor
  Point up (l:ls) rs -> Cursor l (Point up ls (focus:rs))
  Point up [] rs -> focusUp cursor

focusRight :: Cursor -> Cursor
focusRight cursor@(Cursor focus path) = case path of
  Top -> cursor
  Point up ls (r:rs) -> Cursor r (Point up (focus:ls) rs)
  Point up ls [] -> focusDown cursor

focusUp :: Cursor -> Cursor
focusUp cursor@(Cursor focus path) = case path of
  Top -> cursor
  Point up ls rs -> Cursor (Node $ reverse ls ++ focus:rs) up

focusDown :: Cursor -> Cursor
focusDown cursor@(Cursor focus path) = case focus of
  Item _ -> cursor
  Node (n:ns) -> Cursor n (Point path [] ns)

setFocus :: Ast -> Cursor -> Cursor
setFocus ast (Cursor _ path) = Cursor ast path

insertLeft :: Ast -> Cursor -> Cursor
insertLeft ast (Cursor focus (Point up ls rs)) = Cursor ast (Point up ls (focus:rs))

insertRight :: Ast -> Cursor -> Cursor
insertRight ast (Cursor focus (Point up ls rs)) = Cursor ast (Point up (focus:ls) rs)

moveLeft :: Cursor -> Cursor
moveLeft cursor@(Cursor focus path) = case path of
  Top -> cursor
  Point up (l:ls) rs -> Cursor focus (Point up ls (l:rs))
  Point up [] rs -> Cursor focus up

moveRight :: Cursor -> Cursor
moveRight cursor@(Cursor focus path) = case path of
  Top -> cursor
  Point up ls (r:rs) -> Cursor focus (Point up (r:ls) rs)
  Point up ls [] -> Cursor focus up

moveUp :: Cursor -> Cursor
moveUp cursor@(Cursor focus path) = case path of
  Top -> cursor
  Point up ls rs -> Cursor (Node $ reverse ls ++ focus:rs) up

moveDown :: Cursor -> Cursor
moveDown cursor@(Cursor focus path) = case focus of
  Item _ -> cursor
  Node (n:ns) -> Cursor n (Point path [] ns)
  Node [] -> cursor

delete :: Cursor -> Cursor
delete cursor@(Cursor focus path) = case path of
  Top -> cursor
  Point up (l:ls) rs -> Cursor l (Point up ls rs)
  Point up [] (r:rs) -> Cursor r (Point up [] rs)
  Point up [] [] -> Cursor (Node []) up

loop :: Cursor -> IO ()
loop cursor = do
  putStrLn $ render cursor
  putStrLn $ show cursor
  cmd <- getLine
  case cmd of
    "q" -> pure ()
    _ -> loop $ case cmd of
      "t" -> focusDown $ setFocus (Node [Pos]) cursor
      "l" -> moveLeft cursor
      "r" -> moveRight cursor
      "u" -> moveUp cursor

main :: IO ()
main = loop (Cursor Pos Top)