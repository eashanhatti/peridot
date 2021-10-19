{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}

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
  -- PPiName              :: Path Term -> Term -> Term -> Path String
  -- PPiIn                :: Path Term -> String -> Term -> Path Term
  -- PPiOut               :: Path Term -> String -> Term -> Path Term
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
  -- InsertPi           :: Command Term
  SetName            :: String -> Command String
  MoveOut            :: Command a
  MoveRight          :: Command a
  MoveLeft           :: Command a
  MoveIn             :: Command a
  Add                :: Direction -> Command a

data Direction = Left | Right

class MkFT a where focusType :: FocusType a
instance MkFT Term where focusType = FTTerm
instance MkFT String where focusType = FTName
instance MkFT Item where focusType = FTItem

class MkFocus a where focus :: a -> Focus a
instance MkFocus Term where focus e = FTerm e
instance MkFocus Item where focus i = FItem i
instance MkFocus String where focus s = FName s

mkEx :: (MkFT a, MkFocus a) => a -> Path a -> Ex
mkEx f p = Ex $ EditorState (Cursor (focus f) p) focusType

run :: Command a -> EditorState a -> Ex
run command state@(EditorState (Cursor focus path) _) = case command of
  -- InsertLam ns -> Ex $ EditorState (Cursor (FTerm Hole) (PLamBody path ns)) FTTerm
  InsertLam ns -> mkEx Hole (PLamBody path ns)
  InsertApp -> mkEx Hole (PAppTerms path [] [Hole])
  InsertVar s -> mkEx (Var (Name s)) path
  InsertHole -> mkEx Hole path
  InsertLet -> mkEx "_" (PLetName path Hole Hole Hole)
  InsertTermDef -> mkEx "_" (PTermDefName path Hole Hole)
  InsertNamespaceDef -> mkEx "_" (PNamespaceDefName path [])
  -- InsertPi -> Ex $ EditorState (Cursor (FName "_") (PPiName path Hole Hole)) FTName
  SetName s -> mkEx s path
  Add d -> case (path, d) of
    (PLamParams up ln rn body, Left) -> goLamL up ln rn body focus
    (PLamParams up ln rn body, Right) -> goLamR up ln rn body focus
    (PLamAddParam up ln rn body, Left) -> goLamL up ln rn body focus
    (PLamAddParam up ln rn body, Right) -> goLamR up ln rn body focus
    (PAppTerms up le re, Left) -> goAppL up le re focus
    (PAppTerms up le re, Right) -> goAppR up le re focus
    (PAppAddTerm up le re, Left) -> goAppL up le re focus
    (PAppAddTerm up le re, Right) -> goAppR up le re focus
    (PNamespaceDefItems up name li ri, Left) -> goNamespaceL up name li ri focus
    (PNamespaceDefItems up name li ri, Right) -> goNamespaceR up name li ri focus
    (PNamespaceDefAddItem up name li ri, Left) -> goNamespaceL up name li ri focus
    (PNamespaceDefAddItem up name li ri, Right) -> goNamespaceR up name li ri focus
    _ -> Ex state
    where
      goNamespaceR up name li ri focus = mkEx EditorBlankDef (PNamespaceDefAddItem up name (li ++ [unFItem focus]) ri)
      goNamespaceL up name li ri focus =  mkEx EditorBlankDef (PNamespaceDefAddItem up name li (unFItem focus : ri))
      goAppR up le re focus = mkEx EditorBlank (PAppAddTerm up (le ++ [unFTerm focus]) re)
      goAppL up le re focus = mkEx EditorBlank (PAppAddTerm up le (unFTerm focus : re))
      goLamR up ln rn body focus = mkEx "" (PLamAddParam up (ln ++ [unFName focus]) rn body)
      goLamL up ln rn body focus = mkEx "" (PLamAddParam up ln (unFName focus : rn) body)
  MoveRight -> case path of
    PTop -> Ex state
    PLamParams up ln [] body -> mkEx body (PLamBody up (ln ++ [unFName focus]))
    PLamParams up ln (n:rn) body -> mkEx n (PLamParams up (ln ++ [unFName focus]) rn body)
    PLamAddParam up ln rn body -> case (rn, unFName focus) of
      ([], "") -> mkEx body (PLamBody up ln)
      (n:rn, "") -> mkEx n (PLamParams up ln rn body)
      ([], fn) -> mkEx body (PLamBody up (ln ++ [fn]))
      (n:rn, fn) -> mkEx n (PLamParams up (ln ++ [fn]) rn body)
    PLamBody up ns -> run MoveOut state
    PAppAddTerm up le re -> case (re, unFTerm focus) of
      ([], EditorBlank) -> run MoveOut state
      (e:re, EditorBlank) -> mkEx e (PAppTerms up le re)
      ([], fe) -> run MoveOut state
      (e:re, fe) -> mkEx e (PAppTerms up (le ++ [fe]) re)
    PAppTerms up le [] -> run MoveOut state
    PAppTerms up le (r:re) -> mkEx r (PAppTerms up (le ++ [unFTerm focus]) re)
    PLetName up def defTy body -> mkEx defTy (PLetDefTy up (unFName focus) def body)
    PLetDefTy up name def body -> mkEx def (PLetDef up name (unFTerm focus) body)
    PLetDef up name defTy body -> mkEx body (PLetBody up name (unFTerm focus) defTy)
    PLetBody _ _ _ _ -> run MoveOut state
    PTermDefName up ty body -> mkEx ty (PTermDefTy up (unFName focus) body)
    PTermDefTy up name body -> mkEx body (PTermDefBody up name (unFTerm focus))
    PTermDefBody _ _ _ -> run MoveOut state
    PNamespaceDefName up [] -> mkEx EditorBlankDef (PNamespaceDefAddItem up (unFName focus) [] [])
    PNamespaceDefName up (i:is) -> mkEx i (PNamespaceDefItems up (unFName focus) [] is)
    PNamespaceDefItems up name _ [] -> run MoveOut state
    PNamespaceDefItems up name li (i:ri) -> mkEx i (PNamespaceDefItems up name (li ++ [unFItem focus]) ri)
    PNamespaceDefAddItem up name li ri -> case (ri, unFItem focus) of
      ([], EditorBlankDef) -> run MoveOut state
      (i:ri, EditorBlankDef) -> mkEx i (PNamespaceDefItems up name li ri)
      ([], fi) -> run MoveOut state
      (i:ri, fi) -> mkEx i (PNamespaceDefItems up name (li ++ [fi]) ri)
    -- PPiName up inTy outTy -> Ex $ EditorState (Cursor (FTerm inTy) (PPiIn up (unFName focus) outTy)) FTTerm
    -- PPiInTy up name outTy -> Ex $ EditorState (Cursor (FTerm outTy) (PPiOut up name (unFTerm focus))) FTTerm
    -- PPiOut _ _ _ -> run MoveIn state
  MoveLeft -> case path of
    PTop -> Ex state
    PLamParams up [] rn body -> run MoveOut state
    PLamParams up ln rn body -> mkEx (last ln) (PLamParams up (init ln) (unFName focus:rn) body)
    PLamAddParam up ln rn body -> case (length ln, unFName focus) of
      (0, "") -> run MoveOut state
      (_, "") -> mkEx (last ln) (PLamParams up (init ln) rn body)
      (0, fn) -> mkEx "" (PLamAddParam up [] (fn:rn) body)
      (_, fn) -> mkEx (last ln) (PLamParams up (init ln) (fn:rn) body)
    PLamBody up ns -> mkEx (last ns) (PLamParams up (init ns) [] (unFTerm focus))
    PAppTerms up [] re -> run MoveOut state
    PAppTerms up le re -> mkEx (last le) (PAppTerms up (init le) (unFTerm focus:re))
    PAppAddTerm up le re -> case (length le, unFTerm focus) of
      (0, EditorBlank) -> run MoveOut state
      (_, EditorBlank) -> mkEx (last le) (PAppTerms up (init le) re)
      (0, fn) -> mkEx EditorBlank (PAppAddTerm up [] (fn:re))
      (_, fn) -> mkEx (last le) (PAppTerms up (init le) (fn:re))
    PLetName _ _ _ _ -> run MoveOut state
    PLetDefTy up name def body -> mkEx name (PLetName up def (unFTerm focus) body)
    PLetDef up name defTy body -> mkEx defTy (PLetDefTy up name (unFTerm focus) body)
    PLetBody up name def defTy -> mkEx def (PLetDef up name defTy (unFTerm focus))
    PTermDefName up ty body -> run MoveOut state
    PTermDefTy up name body -> mkEx name (PTermDefName up (unFTerm focus) body)
    PTermDefBody up name ty -> mkEx ty (PTermDefTy up name (unFTerm focus))
    PNamespaceDefName up _ -> run MoveOut state
    PNamespaceDefItems up name [] ri -> mkEx name (PNamespaceDefName up ri)
    PNamespaceDefItems up name li ri -> mkEx (last li) (PNamespaceDefItems up name (init li) (unFItem focus : ri))
    PNamespaceDefAddItem up name li ri -> case (length li, unFItem focus) of
      (0, EditorBlankDef) -> mkEx name (PNamespaceDefName up ri)
      (_, EditorBlankDef) -> mkEx (last li) (PNamespaceDefItems up name (init li) ri)
      (0, fi) -> mkEx EditorBlankDef (PNamespaceDefAddItem up name [] (fi:ri))
      (_, fi) -> mkEx (last li) (PNamespaceDefItems up name (init li) (fi:ri))
    -- PPiName _ _ _ -> run MoveOut state
    -- PPiIn up name outTy -> Ex $ EditorState (Cursor (FName name) (PPiName up (unFTerm focus) outTy)) FTName
    -- PPiOut up name inTy -> Ex $ EditorState (Cursor (FTerm inTy) (PPiIn up (unFName focus) outTy)) FTTerm
  MoveOut -> case path of
    PTop -> Ex state
    PLamParams up ln rn body -> mkEx (Lam (map Name ln ++ [Name $ unFName focus] ++ map Name rn) body) up
    PLamBody up ns -> mkEx (Lam (map Name ns) (unFTerm focus)) up
    PLamAddParam up ln rn body ->
      if unFName focus == "" then
        go $ map Name rn
      else
        go $ (Name $ unFName focus) : map Name rn
      where
        go rn = mkEx (Lam (map Name ln ++ rn) body) up
    PAppTerms up le re ->
      let es = le ++ [unFTerm focus] ++ re
      in mkEx (App (head es) (tail es)) up
    PAppAddTerm up le re ->
      let es = if unFTerm focus == EditorBlank then le ++ re else le ++ [unFTerm focus] ++ re
      in mkEx (App (head es) (tail es)) up
    PLetName up def defTy body -> mkEx (Let (Name $ unFName focus) def defTy body) up
    PLetDefTy up name def body -> mkEx (Let (Name name) def (unFTerm focus) body) up
    PLetDef up name defTy body -> mkEx (Let (Name name) (unFTerm focus) defTy body) up
    PLetBody up name def defTy -> mkEx (Let (Name name) def defTy (unFTerm focus)) up
    PTermDefName up ty body -> mkEx (TermDef (Name $ unFName focus) ty body) up
    PTermDefTy up name body -> mkEx (TermDef (Name name) (unFTerm focus) body) up
    PTermDefBody up name ty -> mkEx (TermDef (Name name) ty (unFTerm focus)) up
    PNamespaceDefName up items -> mkEx (NamespaceDef (Name $ unFName focus) items) up
    PNamespaceDefItems up name li ri -> mkEx (NamespaceDef (Name name) (li ++ unFItem focus : ri)) up
    PNamespaceDefAddItem up name li ri ->
      let is = if unFItem focus == EditorBlankDef then li ++ ri else li ++ [unFItem focus] ++ ri
      in mkEx (NamespaceDef (Name name) is) up
    -- PPiName ->
  MoveIn -> case focus of
    FTerm focus -> case focus of
      Lam ns body -> mkEx body (PLamBody path (map unName ns))
      Var _ -> Ex state
      App lam args -> mkEx lam (PAppTerms path [] args)
      Let (Name name) def defTy body -> mkEx body (PLetBody path name def defTy)
    FItem focus -> case focus of
      TermDef (Name n) ty body -> mkEx body (PTermDefBody path n ty)
      NamespaceDef (Name n) items -> case items of
        [] -> mkEx EditorBlankDef (PNamespaceDefAddItem path n [] [])
        i:is -> mkEx i (PNamespaceDefItems path n [] is)
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