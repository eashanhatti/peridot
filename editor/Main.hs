{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}

module Main where

-- import Data.Text
-- import Data.Text.IO(putStrLn)
-- import Prelude hiding(putStrLn)
import TextShow
import TextShow.TH
import Surface
import System.Console.ANSI
import Data.Binary
import Data.Binary.Put
import qualified Data.ByteString.Lazy as B
import Data.List(intersperse)
import Prelude hiding (Left, Right)

data Path a where
  PTop                 :: Path Item
  PTermDefName         :: Path Item -> Term -> Term -> Path String
  PTermDefBody         :: Path Item -> String -> Term -> Path Term
  PTermDefTy           :: Path Item -> String -> Term -> Path Term
  PNamespaceDefName    :: Path Item -> [Item] -> Path String
  PNamespaceDefItems   :: Path Item -> String -> [Item] -> [Item] -> Path Item
  PNamespaceDefAddItem :: Path Item -> String -> [Item] -> [Item] -> Path Item
  PLamParams           :: Path Term -> [String] -> [String] -> Term -> Path String
  PLamAddParam         :: Path Term -> [String] -> [String] -> Term -> Path String
  PLamBody             :: Path Term -> [String] -> Path Term
  PAppTerms            :: Path Term -> [Term] -> [Term] -> Path Term
  PAppAddTerm          :: Path Term -> [Term] -> [Term] -> Path Term
  PLetName             :: Path Term -> Term -> Term -> Term -> Path String
  PLetDefTy            :: Path Term -> String -> Term -> Term -> Path Term
  PLetDef              :: Path Term -> String -> Term -> Term -> Path Term
  PLetBody             :: Path Term -> String -> Term -> Term -> Path Term
deriving instance Show (Path a)

data Focus a where
  FName :: String -> Focus String
  FTerm :: Term -> Focus Term
  FItem :: Item -> Focus Item
deriving instance Show (Focus a)

unFName :: Focus String -> String
unFName (FName s) = s
unFTerm :: Focus Term -> Term
unFTerm (FTerm e) = e
unFItem :: Focus Item -> Item
unFItem (FItem i) = i

data FocusType a where
  FTName :: FocusType String
  FTTerm :: FocusType Term
  FTItem :: FocusType Item

data Cursor a = Cursor { unFocus :: Focus a, unPath :: Path a }
deriving instance Show (Cursor a)

data EditorState a = EditorState { unCursor :: Cursor a, unFocusType :: FocusType a }

data Ex = forall a. Ex { unEx :: EditorState a }

data Command a where
  InsertLam          :: [String] -> Command Term
  InsertApp          :: Command Term
  InsertVar          :: String -> Command Term
  InsertHole         :: Command Term
  InsertLet          :: Command Term
  InsertTermDef      :: Command Item
  InsertNamespaceDef :: Command Item
  SetName            :: String -> Command String
  MoveOut            :: Command a
  MoveRight          :: Command a
  MoveLeft           :: Command a
  MoveIn             :: Command a
  Add                :: Direction -> Command a

data Direction = Left | Right

run :: Command a -> EditorState a -> Ex
run command state@(EditorState (Cursor focus path) _) = case command of
  InsertLam ns -> Ex $ EditorState (Cursor (FTerm Hole) (PLamBody path ns)) FTTerm
  InsertApp -> Ex $ EditorState (Cursor (FTerm Hole) (PAppTerms path [] [Hole])) FTTerm
  InsertVar s -> Ex $ EditorState (Cursor (FTerm $ Var (Name s)) path) FTTerm
  InsertHole -> Ex $ EditorState (Cursor (FTerm Hole) path) FTTerm
  InsertLet -> Ex $ EditorState (Cursor (FName "") (PLetName path Hole Hole Hole)) FTName
  InsertTermDef -> Ex $ EditorState (Cursor (FName "_") (PTermDefName path Hole Hole)) FTName
  InsertNamespaceDef -> Ex $ EditorState (Cursor (FName "_") (PNamespaceDefName path [])) FTName
  SetName s -> Ex $ EditorState (Cursor (FName s) path) FTName
  Add d -> case (path, d) of
    (PLamParams up ln rn body, Left) -> Ex $ EditorState (Cursor (FName "") (PLamAddParam up ln (unFName focus : rn) body)) FTName
    (PLamParams up ln rn body, Right) -> Ex $ EditorState (Cursor (FName "") (PLamAddParam up (ln ++ [unFName focus]) rn body)) FTName
    (PAppTerms up le re, Left) -> Ex $ EditorState (Cursor (FTerm EditorBlank) (PAppAddTerm up le (unFTerm focus : re))) FTTerm
    (PAppTerms up le re, Right) -> Ex $ EditorState (Cursor (FTerm EditorBlank) (PAppAddTerm up (le ++ [unFTerm focus]) re)) FTTerm
    (PNamespaceDefItems up name li ri, Left) ->
      Ex $ EditorState (Cursor (FItem EditorBlankDef) (PNamespaceDefAddItem up name li (unFItem focus : ri))) FTItem
    (PNamespaceDefItems up name li ri, Right) ->
      Ex $ EditorState (Cursor (FItem EditorBlankDef) (PNamespaceDefAddItem up name (li ++ [unFItem focus]) ri)) FTItem
    _ -> Ex state
  MoveRight -> case path of
    PTop -> Ex state
    PLamParams up ln [] body -> Ex $ EditorState (Cursor (FTerm body) (PLamBody up (ln ++ [unFName focus]))) FTTerm
    PLamParams up ln (n:rn) body -> Ex $ EditorState (Cursor (FName n) (PLamParams up (ln ++ [unFName focus]) rn body)) FTName
    PLamAddParam up ln rn body -> case (rn, unFName focus) of
      ([], "") -> Ex $ EditorState (Cursor (FTerm body) (PLamBody up ln)) FTTerm
      (n:rn, "") -> Ex $ EditorState (Cursor (FName n) (PLamParams up ln rn body)) FTName
      ([], fn) -> Ex $ EditorState (Cursor (FTerm body) (PLamBody up (ln ++ [fn]))) FTTerm
      (n:rn, fn) -> Ex $ EditorState (Cursor (FName n) (PLamParams up (ln ++ [fn]) rn body)) FTName
    PLamBody up ns -> run MoveOut state
    PAppAddTerm up le re -> case (re, unFTerm focus) of
      ([], EditorBlank) -> run MoveOut state
      (e:re, EditorBlank) -> Ex $ EditorState (Cursor (FTerm e) (PAppTerms up le re)) FTTerm
      ([], fe) -> run MoveOut state
      (e:re, fe) -> Ex $ EditorState (Cursor (FTerm e) (PAppTerms up (le ++ [fe]) re)) FTTerm
    PAppTerms up le [] -> run MoveOut state
    PAppTerms up le (r:re) -> Ex $ EditorState (Cursor (FTerm r) (PAppTerms up (le ++ [unFTerm focus]) re)) FTTerm
    PLetName up def defTy body -> Ex $ EditorState (Cursor (FTerm defTy) (PLetDefTy up (unFName focus) def body)) FTTerm
    PLetDefTy up name def body -> Ex $ EditorState (Cursor (FTerm def) (PLetDef up name (unFTerm focus) body)) FTTerm
    PLetDef up name defTy body -> Ex $ EditorState (Cursor (FTerm body) (PLetBody up name (unFTerm focus) defTy)) FTTerm
    PLetBody _ _ _ _ -> run MoveOut state
    PTermDefName up ty body -> Ex $ EditorState (Cursor (FTerm ty) (PTermDefTy up (unFName focus) body)) FTTerm
    PTermDefTy up name body -> Ex $ EditorState (Cursor (FTerm body) (PTermDefBody up name (unFTerm focus))) FTTerm
    PTermDefBody _ _ _ -> run MoveOut state
    PNamespaceDefName up [] -> Ex $ EditorState (Cursor (FItem EditorBlankDef) (PNamespaceDefAddItem up (unFName focus) [] [])) FTItem
    PNamespaceDefName up (i:is) -> Ex $ EditorState (Cursor (FItem i) (PNamespaceDefItems up (unFName focus) [] is)) FTItem
    PNamespaceDefItems up name _ [] -> run MoveOut state
    PNamespaceDefItems up name li (i:ri) -> Ex $ EditorState (Cursor (FItem i) (PNamespaceDefItems up name (li ++ [unFItem focus]) ri)) FTItem
    PNamespaceDefAddItem up name li ri -> case (ri, unFItem focus) of
      ([], EditorBlankDef) -> run MoveOut state
      (i:ri, EditorBlankDef) -> Ex $ EditorState (Cursor (FItem i) (PNamespaceDefItems up name li ri)) FTItem
      ([], fi) -> run MoveOut state
      (i:ri, fi) -> Ex $ EditorState (Cursor (FItem i) (PNamespaceDefItems up name (li ++ [fi]) ri)) FTItem
  MoveLeft -> case path of
    PTop -> Ex state
    PLamParams up [] rn body -> run MoveOut state
    PLamParams up ln rn body -> Ex $ EditorState (Cursor (FName (last ln)) (PLamParams up (init ln) (unFName focus:rn) body)) FTName
    PLamAddParam up ln rn body -> case (length ln, unFName focus) of
      (0, "") -> run MoveOut state
      (_, "") -> Ex $ EditorState (Cursor (FName $ last ln) (PLamParams up (init ln) rn body)) FTName
      (0, fn) -> Ex $ EditorState (Cursor (FName "") (PLamAddParam up [] (fn:rn) body)) FTName
      (_, fn) -> Ex $ EditorState (Cursor (FName $ last ln) (PLamParams up (init ln) (fn:rn) body)) FTName
    PLamBody up ns -> Ex $ EditorState (Cursor (FName $ last ns) (PLamParams up (init ns) [] (unFTerm focus))) FTName
    PAppTerms up [] re -> run MoveOut state
    PAppTerms up le re -> Ex $ EditorState (Cursor (FTerm $ last le) (PAppTerms up (init le) (unFTerm focus:re))) FTTerm
    PAppAddTerm up le re -> case (length le, unFTerm focus) of
      (0, EditorBlank) -> run MoveOut state
      (_, EditorBlank) -> Ex $ EditorState (Cursor (FTerm $ last le) (PAppTerms up (init le) re)) FTTerm
      (0, fn) -> Ex $ EditorState (Cursor (FTerm EditorBlank) (PAppAddTerm up [] (fn:re))) FTTerm
      (_, fn) -> Ex $ EditorState (Cursor (FTerm $ last le) (PAppTerms up (init le) (fn:re))) FTTerm
    PLetName _ _ _ _ -> run MoveOut state
    PLetDefTy up name def body -> Ex $ EditorState (Cursor (FName name) (PLetName up def (unFTerm focus) body)) FTName
    PLetDef up name defTy body -> Ex $ EditorState (Cursor (FTerm defTy) (PLetDefTy up name (unFTerm focus) body)) FTTerm
    PLetBody up name def defTy -> Ex $ EditorState (Cursor (FTerm def) (PLetDef up name defTy (unFTerm focus))) FTTerm
    PTermDefName up ty body -> run MoveOut state
    PTermDefTy up name body -> Ex $ EditorState (Cursor (FName name) (PTermDefName up (unFTerm focus) body)) FTName
    PTermDefBody up name ty -> Ex $ EditorState (Cursor (FTerm ty) (PTermDefTy up name (unFTerm focus))) FTTerm
    PNamespaceDefName up _ -> run MoveOut state
    PNamespaceDefItems up name [] ri -> Ex $ EditorState (Cursor (FName name) (PNamespaceDefName up ri)) FTName
    PNamespaceDefItems up name li ri -> Ex $ EditorState (Cursor (FItem (last li)) (PNamespaceDefItems up name (init li) (unFItem focus : ri))) FTItem
    PNamespaceDefAddItem up name li ri -> case (length li, unFItem focus) of
      (0, EditorBlankDef) -> Ex $ EditorState (Cursor (FName name) (PNamespaceDefName up ri)) FTName
      (_, EditorBlankDef) -> Ex $ EditorState (Cursor (FItem $ last li) (PNamespaceDefItems up name (init li) ri)) FTItem
      (0, fi) -> Ex $ EditorState (Cursor (FItem EditorBlankDef) (PNamespaceDefAddItem up name [] (fi:ri))) FTItem
      (_, fi) -> Ex $ EditorState (Cursor (FItem $ last li) (PNamespaceDefItems up name (init li) (fi:ri))) FTItem
  MoveOut -> case path of
    PTop -> Ex state
    PLamParams up ln rn body -> Ex $ EditorState (Cursor (FTerm (Lam (map Name ln ++ [Name $ unFName focus] ++ map Name rn) body)) up) FTTerm
    PLamBody up ns -> Ex $ EditorState (Cursor (FTerm $ Lam (map Name ns) (unFTerm focus)) up) FTTerm
    PLamAddParam up ln rn body ->
      if unFName focus == "" then
        go $ map Name rn
      else
        go $ (Name $ unFName focus) : map Name rn
      where
        go rn = Ex $ EditorState (Cursor (FTerm $ Lam (map Name ln ++ rn) body) up) FTTerm
    PAppTerms up le re ->
      let es = le ++ [unFTerm focus] ++ re
      in Ex $ EditorState (Cursor (FTerm $ App (head es) (tail es)) up) FTTerm
    PAppAddTerm up le re ->
      let es = if unFTerm focus == EditorBlank then le ++ re else le ++ [unFTerm focus] ++ re
      in Ex $ EditorState (Cursor (FTerm $ App (head es) (tail es)) up) FTTerm
    PLetName up def defTy body -> Ex $ EditorState (Cursor (FTerm $ Let (Name $ unFName focus) def defTy body) up) FTTerm
    PLetDefTy up name def body -> Ex $ EditorState (Cursor (FTerm $ Let (Name name) def (unFTerm focus) body) up) FTTerm
    PLetDef up name defTy body -> Ex $ EditorState (Cursor (FTerm $ Let (Name name) (unFTerm focus) defTy body) up) FTTerm
    PLetBody up name def defTy -> Ex $ EditorState (Cursor (FTerm $ Let (Name name) def defTy (unFTerm focus)) up) FTTerm
    PTermDefName up ty body -> Ex $ EditorState (Cursor (FItem $ TermDef (Name $ unFName focus) ty body) up) FTItem
    PTermDefTy up name body -> Ex $ EditorState (Cursor (FItem $ TermDef (Name name) (unFTerm focus) body) up) FTItem
    PTermDefBody up name ty -> Ex $ EditorState (Cursor (FItem $ TermDef (Name name) ty (unFTerm focus)) up) FTItem
    PNamespaceDefName up items -> Ex $ EditorState (Cursor (FItem $ NamespaceDef (Name $ unFName focus) items) up) FTItem
    PNamespaceDefItems up name li ri -> Ex $ EditorState (Cursor (FItem $ NamespaceDef (Name name) (li ++ unFItem focus : ri)) up) FTItem
    PNamespaceDefAddItem up name li ri ->
      let is = if unFItem focus == EditorBlankDef then li ++ ri else li ++ [unFItem focus] ++ ri
      in Ex $ EditorState (Cursor (FItem $ NamespaceDef (Name name) is) up) FTItem
  MoveIn -> case focus of
    FTerm focus -> case focus of
      Lam ns body -> Ex $ EditorState (Cursor (FTerm body) (PLamBody path (map unName ns))) FTTerm
      Var _ -> Ex state
      App lam args -> Ex $ EditorState (Cursor (FTerm lam) (PAppTerms path [] args)) FTTerm
      Let (Name name) def defTy body -> Ex $ EditorState (Cursor (FTerm body) (PLetBody path name def defTy)) FTTerm
    FItem focus -> case focus of
      TermDef (Name n) ty body -> Ex $ EditorState (Cursor (FTerm body) (PTermDefBody path n ty)) FTTerm
      NamespaceDef (Name n) items -> case items of
        [] -> Ex $ EditorState (Cursor (FItem EditorBlankDef) (PNamespaceDefAddItem path n [] [])) FTItem
        i:is -> Ex $ EditorState (Cursor (FItem i) (PNamespaceDefItems path n [] is)) FTItem
    FName _ -> Ex state

putWord16 :: Word16 -> Put
putWord16 = put

putItem :: Item -> Put
putItem item = case item of
  TermDef (Name n) ty body -> do
    putWord8 1
    putString n
    putTerm ty
    putTerm body

putString :: String -> Put
putString s = do
  putWord16 $ fromIntegral (length s)
  loop s
  where
    loop s = case s of
      [] -> pure ()
      c:cs -> do
        put c
        loop cs

putStrings :: [String] -> Put
putStrings ss = case ss of
  [] -> pure ()
  s:ss -> do
    putString s
    putStrings ss

putTerm :: Term -> Put
putTerm term = case term of
  Var (Name name) -> do
    putWord8 0
    putString name
  -- GVar (GName name) -> do
  --   putWord8 1
  --   put (fromIntegral (length s) :: Word16)
  --   putStrings name
  Lam names body -> do
    putWord8 2
    putWord16 $ fromIntegral (length names)
    putStrings (map unName names)
    putTerm body
  Hole -> putWord8 12

export :: EditorState a -> String -> IO ()
export state@(EditorState cursor _) fn = do
  let program = loop (Ex state) 
  let bs = runPut $ putItem program
  B.writeFile fn bs
  where
    loop :: Ex -> Item
    loop (Ex state) =
      case run MoveOut state of
        ex@(Ex (EditorState (Cursor focus path) _)) -> case path of
          PTop -> case focus of FItem item -> item
          _ -> loop ex

render :: EditorState a -> String
render (EditorState (Cursor focus path) _) = renderPath ("[" ++ renderFocus focus ++ "]") (simpleFocus focus) path where
  renderFocus :: Focus a -> String
  renderFocus focus = case focus of
    FName s -> s
    FTerm term -> renderTerm term
    FItem item -> renderItem item
  renderTerm :: Term -> String
  renderTerm term = case term of
    Lam names body -> "\\" ++ snames (map unName names) ++ ". " ++ renderTerm body
    App lam args ->
      let se = if simple lam then renderTerm lam else "(" ++ renderTerm lam ++ ")"
      in se ++ space args ++ sterms args
    Var (Name s) -> s
    Hole -> "?"
    Let (Name name) def defTy body -> "let " ++ name ++ " : " ++ renderTerm defTy ++ " = " ++ renderTerm def ++ "\nin " ++ renderTerm body
    EditorBlank -> ""
  renderItem :: Item -> String
  renderItem item = case item of
    TermDef (Name n) ty body -> "def " ++ n ++ " : " ++ renderTerm ty ++ " =\n" ++ (indent $ renderTerm body)
    NamespaceDef (Name n) items -> "namespace " ++ n ++ newline items ++ indent (sitems items)
    EditorBlankDef -> ""
  renderPath :: String -> Bool -> Path a -> String
  renderPath focus isSimple path = case path of
    PTop -> focus
    PLamBody up names -> renderPath ("\\" ++ snames names ++ ". " ++ focus) False up
    PLamParams up ln rn body -> renderPath ("\\" ++ snames ln ++ focus ++ snames rn ++ ". " ++ renderTerm body) False up
    PLamAddParam up ln rn body -> renderPath ("\\" ++ snames ln ++ focus ++ snames rn ++ ". " ++ renderTerm body) False up
    PAppTerms up le re -> renderApp up le re isSimple focus
    PAppAddTerm up le re -> renderApp up le re isSimple focus
    PLetName up def defTy body ->
      renderPath ("let " ++ focus ++ " : " ++ renderTerm defTy ++ " = " ++ renderTerm def ++ "\nin " ++ renderTerm body) False up
    PLetDef up name defTy body ->
      renderPath ("let " ++ name ++ " : " ++ renderTerm defTy ++ " = " ++ focus ++ "\nin " ++ renderTerm body) False up
    PLetDefTy up name def body ->
      renderPath ("let " ++ name ++ " : " ++ focus ++ " = " ++ renderTerm def ++ "\nin " ++ renderTerm body) False up
    PLetBody up name def defTy ->
      renderPath ("let " ++ name ++ " : " ++ renderTerm defTy ++ " = " ++ renderTerm def ++ "\nin " ++ focus) False up
    PTermDefName up ty body -> renderPath ("def " ++ focus ++ " : " ++ renderTerm ty ++ " =\n" ++ indent (renderTerm body)) False up
    PTermDefTy up name body -> renderPath ("def " ++ name ++ " : " ++ focus ++ " =\n" ++ indent (renderTerm body)) False up
    PTermDefBody up name ty -> renderPath ("def " ++ name ++ " : " ++ renderTerm ty ++ " =\n" ++ indent focus) False up
    PNamespaceDefName up items -> renderPath ("namespace " ++ focus ++ "\n" ++ indent (sitems items)) False up
    PNamespaceDefItems up name li ri -> renderNamespace up name li ri focus
    PNamespaceDefAddItem up name li ri -> renderNamespace up name li ri focus

  renderNamespace up name li ri focus = renderPath ("namespace " ++ name ++ "\n" ++ indent (sitems li ++ newline li ++ focus ++ newline ri ++ sitems ri)) False up
  renderApp up le re isSimple focus = renderPath (sterms le ++ space le ++ parenFocus isSimple focus ++ space re ++ sterms re) False up
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
  newline cs = case cs of
    [] -> ""
    _ -> "\n"
  sterms es = case es of
    [] -> ""
    e:es ->
      let se = if simple e then renderTerm e else "(" ++ renderTerm e ++ ")"
      in se ++ space es ++ sterms es
  snames ns = case ns of
    [] -> ""
    n:ns -> n ++ " " ++ snames ns
  sitems is = case is of
    [] -> ""
    i:is -> renderItem i ++ "\n" ++ sitems is
  indent s = concat $ intersperse "\n" $ map ("  "++) (lines s)

loop :: EditorState a -> IO ()
loop state = do
  -- clearScreen
  putStrLn (show $ unCursor state)
  putStrLn (render state)
  s <- getLine
  state <- case (s, unFocusType state) of
    ("e", _) -> do
      fn <- getLine
      export state fn
      pure $ Ex state
    ("r", _) -> pure $ run MoveRight state
    ("l", _) -> pure $ run MoveLeft state
    ("o", _) -> pure $ run MoveOut state
    ("i", _) -> pure $ run MoveIn state
    (" l", _) -> pure $ run (Add Left) state
    (" r", _) -> pure $ run (Add Right) state
    ("d", FTTerm) -> pure $ run InsertHole state
    ("lam", FTTerm) -> do
      n <- getLine
      pure $ if n /= "" then run (InsertLam $ words n) state else Ex state
    ("let", FTTerm) -> pure $ run InsertLet state
    ("app", FTTerm) -> pure $ run InsertApp state
    ("ns", FTItem) -> pure $ run InsertNamespaceDef state
    ("def", FTItem) -> pure $ run InsertTermDef state
    (_, FTTerm) -> pure $ run (InsertVar s) state
    (_, FTName) -> pure $ if s == "" then Ex state else run (SetName s) state
  next state
  where
    next :: Ex -> IO ()
    next (Ex state) = loop state

main :: IO ()
main = loop (EditorState (Cursor (FItem $ NamespaceDef (Name "main") []) PTop) FTItem)