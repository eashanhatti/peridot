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
import Data.Binary.Get(runGet)
import qualified Data.ByteString.Lazy as B
import Data.List(intersperse)
import Prelude hiding (Left, Right)
import Parsing(getItem)

data Con = Con String Term | EditorBlankCon
  deriving Show

data Path a where
  PTop                 :: Path Item
  PTermDefName         :: Path Item -> Term -> Term -> Path String
  PTermDefBody         :: Path Item -> String -> Term -> Path Term
  PTermDefTy           :: Path Item -> String -> Term -> Path Term
  PNamespaceDefName    :: Path Item -> [Item] -> Path String
  PNamespaceDefItems   :: Path Item -> String -> [Item] -> [Item] -> Path Item
  PNamespaceDefAddItem :: Path Item -> String -> [Item] -> [Item] -> Path Item
  PIndDefName          :: Path Item -> Term -> [Con] -> Path String
  PIndDefTy            :: Path Item -> String -> [Con] -> Path Term
  PIndDefCons          :: Path Item -> String -> Term -> [Con] -> [Con] -> Path Con
  PIndDefAddCon        :: Path Item -> String -> Term -> [Con] -> [Con] -> Path Con
  PConName             :: Path Con  -> Term -> Path String
  PConTy               :: Path Con  -> String -> Path Term
  PLamParams           :: Path Term -> [String] -> [String] -> Term -> Path String
  PLamAddParam         :: Path Term -> [String] -> [String] -> Term -> Path String
  PLamBody             :: Path Term -> [String] -> Path Term
  PAppTerms            :: Path Term -> [Term] -> [Term] -> Path Term
  PAppAddTerm          :: Path Term -> [Term] -> [Term] -> Path Term
  PLetName             :: Path Term -> Term -> Term -> Term -> Path String
  PLetDefTy            :: Path Term -> String -> Term -> Term -> Path Term
  PLetDef              :: Path Term -> String -> Term -> Term -> Path Term
  PLetBody             :: Path Term -> String -> Term -> Term -> Path Term
  PPiName              :: Path Term -> Term -> Term -> Path String
  PPiIn                :: Path Term -> String -> Term -> Path Term
  PPiOut               :: Path Term -> String -> Term -> Path Term
  PCode                :: Path Term -> Path Term
  PQuote               :: Path Term -> Path Term
  PSplice              :: Path Term -> Path Term
deriving instance Show (Path a)

data Focus a where
  FName :: String -> Focus String
  FTerm :: Term -> Focus Term
  FItem :: Item -> Focus Item
  FCon  :: Con -> Focus Con
deriving instance Show (Focus a)

unFName :: Focus String -> String
unFName (FName s) = s
unFTerm :: Focus Term -> Term
unFTerm (FTerm e) = e
unFItem :: Focus Item -> Item
unFItem (FItem i) = i
unFCon :: Focus Con -> Con
unFCon  (FCon c)  = c

data FocusType a where
  FTName :: FocusType String
  FTTerm :: FocusType Term
  FTItem :: FocusType Item
  FTCon  :: FocusType Con

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
  InsertIndDef       :: Command Item
  InsertPi           :: Command Term
  InsertU1           :: Command Term
  InsertU0           :: Command Term
  InsertCode         :: Command Term
  InsertQuote        :: Command Term
  InsertSplice       :: Command Term
  InsertGVar         :: [String] -> Command Term
  InsertCon          :: String -> Command Con
  SetName            :: String -> Command String
  MoveOut            :: Command a
  MoveRight          :: Command a
  MoveLeft           :: Command a
  MoveIn             :: Command a
  Add                :: Direction -> Command a

data Direction = Left | Right

class MkFT a where focusType :: FocusType a
instance MkFT Term where   focusType = FTTerm
instance MkFT String where focusType = FTName
instance MkFT Item where   focusType = FTItem
instance MkFT Con where    focusType = FTCon

class MkFocus a where focus :: a -> Focus a
instance MkFocus Term where   focus = FTerm
instance MkFocus Item where   focus = FItem
instance MkFocus String where focus = FName
instance MkFocus Con where    focus = FCon

mkEx :: (MkFT a, MkFocus a) => a -> Path a -> Ex
mkEx f p = Ex $ EditorState (Cursor (focus f) p) focusType

run :: Command a -> EditorState a -> Ex
run command state@(EditorState (Cursor focus path) _) = case command of
  InsertLam ns -> mkEx Hole (PLamBody path ns)
  InsertApp -> mkEx Hole (PAppTerms path [] [Hole])
  InsertVar s -> mkEx (Var (Name s)) path
  InsertHole -> mkEx Hole path
  InsertLet -> mkEx "_" (PLetName path Hole Hole Hole)
  InsertTermDef -> mkEx "_" (PTermDefName path Hole Hole)
  InsertNamespaceDef -> mkEx "_" (PNamespaceDefName path [])
  InsertIndDef -> mkEx "_" (PIndDefName path Hole [])
  InsertPi -> mkEx "_" (PPiName path Hole Hole)
  InsertU0 -> mkEx U0 path
  InsertU1 -> mkEx U1 path
  InsertCode -> mkEx Hole (PCode path)
  InsertQuote -> mkEx Hole (PQuote path)
  InsertSplice -> mkEx Hole (PSplice path)
  InsertGVar ns -> mkEx (GVar $ GName ns) path
  InsertCon n -> mkEx (Con n Hole) path
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
    (PIndDefCons up name ty lc rc, Right) -> goIndR up name ty lc rc focus
    (PIndDefAddCon up name ty lc rc, Right) -> goIndR up name ty lc rc focus
    _ -> Ex state
    where
      goIndR up name ty lc rc focus = mkEx EditorBlankCon (PIndDefAddCon up name ty (lc ++ [unFCon focus]) rc)
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
    PPiName up inTy outTy -> mkEx inTy (PPiIn up (unFName focus) outTy)
    PPiIn up name outTy -> mkEx outTy (PPiOut up name (unFTerm focus))
    PPiOut _ _ _ -> run MoveIn state
    PCode _ -> run MoveIn state
    PQuote _ -> run MoveIn state
    PSplice _ -> run MoveIn state
    PIndDefName up ty cons -> mkEx ty (PIndDefTy up (unFName focus) cons)
    PIndDefTy up name [] -> mkEx EditorBlankCon (PIndDefAddCon up name (unFTerm focus) [] []) 
    PIndDefTy up name (c:cs) -> mkEx c (PIndDefCons up name (unFTerm focus) [] cs)
    PIndDefCons up name ty lc [] -> run MoveOut state
    PIndDefCons up name ty lc (c:rc) -> mkEx c (PIndDefCons up name ty (lc ++ [unFCon focus]) rc)
    PIndDefAddCon up name ty lc rc -> case (rc, unFCon focus) of
      ([], EditorBlankCon) -> run MoveOut state
      (c:rc, EditorBlankCon) -> mkEx c (PIndDefCons up name ty lc rc)
      ([], fc) -> run MoveOut state
      (c:rc, fc) -> mkEx c (PIndDefCons up name ty (lc ++ [fc]) rc)
    PConName up ty -> mkEx ty (PConTy up (unFName focus))
    PConTy _ _ -> run MoveOut state
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
    PPiName _ _ _ -> run MoveOut state
    PPiIn up name outTy -> mkEx name (PPiName up (unFTerm focus) outTy)
    PPiOut up name inTy -> mkEx inTy (PPiIn up name (unFTerm focus))
    PCode _ -> run MoveOut state
    PQuote _ -> run MoveOut state
    PSplice _ -> run MoveOut state
    PIndDefName _ _ _ -> run MoveOut state
    PIndDefTy up name cons -> mkEx name (PIndDefName up (unFTerm focus) cons)
    PIndDefCons up name ty [] rc -> mkEx ty (PIndDefTy up name rc)
    PIndDefCons up name ty lc rc -> mkEx (last lc) (PIndDefCons up name ty (init lc) (unFCon focus : rc))
    PIndDefAddCon up name ty lc rc -> case (length lc, unFCon focus) of
      (0, EditorBlankCon) -> mkEx ty (PIndDefTy up name rc)
      (_, EditorBlankCon) -> mkEx (last lc) (PIndDefCons up name ty (init lc) rc)
      (0, fc) -> mkEx ty (PIndDefTy up name (fc:rc))
      (_, fc) -> mkEx (last lc) (PIndDefCons up name ty (init lc) (fc:rc))
    PConName _ _ -> run MoveOut state
    PConTy up name -> mkEx name (PConName up (unFTerm focus))
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
    PPiName up inTy outTy -> mkEx (Pi (Name $ unFName focus) inTy outTy) up
    PPiIn up name outTy -> mkEx (Pi (Name name) (unFTerm focus) outTy) up
    PPiOut up name inTy -> mkEx (Pi (Name name) inTy (unFTerm focus)) up
    PCode up -> mkEx (Code $ unFTerm focus) up
    PQuote up -> mkEx (Quote $ unFTerm focus) up
    PSplice up -> mkEx (Splice $ unFTerm focus) up
    PIndDefName up ty cons -> mkEx (IndDef (Name $ unFName focus) ty (map (\(Con n t) -> (Name n, t)) cons)) up
    PIndDefTy up name cons -> mkEx (IndDef (Name name) (unFTerm focus) (map (\(Con n t) -> (Name n, t)) cons)) up
    PIndDefCons up name ty lc rc ->
      let (Con n t) = unFCon focus
      in mkEx (IndDef (Name name) ty (map (\(Con n t) -> (Name n, t)) lc ++ (Name n, t) : map (\(Con n t) -> (Name n, t)) rc)) up
    PIndDefAddCon up name ty lc rc ->
      let
        clc = map (\(Con n t) -> (Name n, t)) lc
        crc = map (\(Con n t) -> (Name n, t)) rc
        cs =
          case unFCon focus of
            EditorBlankCon -> clc ++ crc
            Con n t -> clc ++ (Name n, t):crc
      in mkEx (IndDef (Name name) ty cs) up
    PConName up ty -> mkEx (Con (unFName focus) ty) up
    PConTy up name -> mkEx (Con name (unFTerm focus)) up
  MoveIn -> case focus of
    FTerm focus -> case focus of
      Lam ns body -> mkEx body (PLamBody path (map unName ns))
      Var _ -> Ex state
      GVar _ -> Ex state
      App lam args -> mkEx lam (PAppTerms path [] args)
      Let (Name name) def defTy body -> mkEx body (PLetBody path name def defTy)
      Pi (Name "_") inTy outTy -> mkEx inTy (PPiIn path "_" outTy)
      Pi (Name name) inTy outTy -> mkEx name (PPiName path inTy outTy)
      U0 -> Ex state
      U1 -> Ex state
      Code ty -> mkEx ty (PCode path)
      Quote e -> mkEx e (PQuote path)
      Splice e -> mkEx e (PSplice path)
    FItem focus -> case focus of
      TermDef (Name n) ty body -> mkEx body (PTermDefBody path n ty)
      NamespaceDef (Name n) items -> case items of
        [] -> mkEx EditorBlankDef (PNamespaceDefAddItem path n [] [])
        i:is -> mkEx i (PNamespaceDefItems path n [] is)
      IndDef (Name n) ty cons -> case cons of
        [] -> mkEx EditorBlankCon (PIndDefAddCon path n ty [] [])
        (Name cn, cty):cs -> mkEx (Con cn cty) (PIndDefCons path n ty [] (map (\(Name n, t) -> Con n t) cs))
    FName _ -> Ex state
    FCon (Con name ty) -> mkEx name (PConName path ty)

putWord16 :: Word16 -> Put
putWord16 = put

putItem :: Item -> Put
putItem item = case item of
  NamespaceDef (Name n) items -> do
    putWord8 0
    putString n
    putWord16 $ fromIntegral (length items)
    loop items
    where
      loop is = case is of
        [] -> pure ()
        i:is -> do
          putItem i
          loop is
  TermDef (Name n) ty body -> do
    putWord8 1
    putString n
    putTerm ty
    putTerm body
  IndDef (Name n) ty cons -> do
    putWord8 2
    putString n
    putTerm ty
    putWord16 $ fromIntegral (length cons)
    loop cons
    where
      loop cs = case cs of
        [] -> pure ()
        (Name n, t):cs -> do
          putString n
          putTerm t
          loop cs

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
  GVar (GName name) -> do
    putWord8 1
    putWord16 $ fromIntegral (length name)
    putStrings name
  Lam names body -> do
    putWord8 2
    putWord16 $ fromIntegral (length names)
    putStrings (map unName names)
    putTerm body
  App lam args -> do
    putWord8 3
    putWord16 $ fromIntegral (length args)
    loop args
    where
      loop as = case as of
        [] -> pure ()
        a:as -> do
          putTerm a
          loop as
  Pi (Name name) inTy outTy -> do
    putWord8 5
    putString name
    putTerm inTy
    putTerm outTy
  Let (Name name) def defTy body -> do
    putWord8 6
    putString name
    putTerm def
    putTerm defTy
    putTerm body
  U1 -> putWord8 7
  U0 -> putWord8 8
  Code ty -> do
    putWord8 9
    putTerm ty
  Quote e -> do
    putWord8 10
    putTerm e
  Splice e -> do
    putWord8 11
    putTerm e
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
    FCon (Con name ty) -> name ++ " : " ++ renderTerm ty
    FCon EditorBlankCon -> ""
  renderTerm :: Term -> String
  renderTerm term = case term of
    Lam names body -> "\\" ++ snames (map unName names) ++ ". " ++ renderTerm body
    App lam args ->
      let se = if simple lam then renderTerm lam else "(" ++ renderTerm lam ++ ")"
      in se ++ space args ++ sterms args
    Var (Name s) -> s
    GVar (GName ns) -> concat $ intersperse "." $ reverse ns
    Hole -> "?"
    Let (Name name) def defTy body -> "let " ++ name ++ " : " ++ renderTerm defTy ++ " = " ++ renderTerm def ++ "\nin " ++ renderTerm body
    Pi (Name "_") inTy outTy -> renderTerm inTy ++ " -> " ++ renderTerm outTy
    Pi (Name name) inTy outTy -> "(" ++ name ++ " : " ++ renderTerm inTy ++ ") -> " ++ renderTerm outTy
    U0 -> "U0"
    U1 -> "U1"
    Code ty -> "Code " ++ parenFocus (simple ty) (renderTerm ty)
    Quote e -> "<" ++ renderTerm e ++ ">"
    Splice e -> "~" ++ parenFocus (simple e) (renderTerm e)
    EditorBlank -> ""
  renderItem :: Item -> String
  renderItem item = case item of
    TermDef (Name n) ty body -> "\ESC[32;1mdef\ESC[0m " ++ n ++ " : " ++ renderTerm ty ++ " =\n" ++ (indent $ renderTerm body)
    NamespaceDef (Name n) items -> "\ESC[32;1mnamespace\ESC[0m " ++ n ++ newline items ++ indent (sitems items)
    IndDef (Name n) ty cons -> "\ESC[32;1minductive\ESC[0m " ++ n ++ " : " ++ renderTerm ty ++ newline cons ++ (indent $ scons (map (\(Name n, t) -> Con n t) cons))
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
    PTermDefName up ty body -> renderPath ("\ESC[32;1mdef\ESC[0m " ++ focus ++ " : " ++ renderTerm ty ++ " =\n" ++ indent (renderTerm body)) False up
    PTermDefTy up name body -> renderPath ("\ESC[32;1mdef\ESC[0m " ++ name ++ " : " ++ focus ++ " =\n" ++ indent (renderTerm body)) False up
    PTermDefBody up name ty -> renderPath ("\ESC[32;1mdef\ESC[0m " ++ name ++ " : " ++ renderTerm ty ++ " =\n" ++ indent focus) False up
    PNamespaceDefName up items -> renderPath ("\ESC[32;1mnamespace\ESC[0m " ++ focus ++ "\n" ++ indent (sitems items)) False up
    PNamespaceDefItems up name li ri -> renderNamespace up name li ri focus
    PNamespaceDefAddItem up name li ri -> renderNamespace up name li ri focus
    PPiName up inTy outTy -> renderPath ("(" ++ focus ++ " : " ++ renderTerm inTy ++ ") -> " ++ renderTerm outTy) False up
    PPiIn up name outTy -> renderPi up name focus (renderTerm outTy)
    PPiOut up name inTy -> renderPi up name (renderTerm inTy) focus
    PCode up -> renderPath ("Code " ++ parenFocus isSimple focus) False up
    PQuote up -> renderPath ("<" ++ focus ++ ">") True up
    PSplice up -> renderPath ("~" ++ parenFocus isSimple focus) False up
    PIndDefName up ty cons -> renderPath ("\ESC[32;1minductive\ESC[0m " ++ focus ++ " : " ++ renderTerm ty ++ "\n" ++ (indent $ scons cons)) False up
    PIndDefTy up name cons -> renderPath ("\ESC[32;1minductive\ESC[0m " ++ name ++ " : " ++ focus ++ "\n" ++ (indent $ scons cons)) False up
    PIndDefCons up name ty lc rc -> renderCons up name ty lc rc focus
    PIndDefAddCon up name ty lc rc -> renderCons up name ty lc rc focus
    PConName up ty -> renderPath (focus ++ " : " ++ renderTerm ty) False up
    PConTy up name -> renderPath (name ++ " : " ++ focus) False up

  renderCons up name ty lc rc focus = renderPath ("\ESC[32;1minductive\ESC[0m " ++ name ++ " : " ++ renderTerm ty ++ "\n" ++ indent cons) False up
    where
      cons = scons lc ++ focus ++ newline rc ++ scons rc
  renderPi up name inTy outTy = (\s -> renderPath s False up) $ case name of
      "_" -> inTy ++ " -> " ++ outTy
      _ -> "(" ++ name ++ " : " ++ inTy ++ ") -> " ++ outTy
  renderNamespace up name li ri focus = renderPath ("\ESC[32;1mnamespace\ESC[0m " ++ name ++ "\n" ++ indent (sitems li ++ newline li ++ focus ++ newline ri ++ sitems ri)) False up
  renderApp up le re isSimple focus = renderPath (sterms le ++ space le ++ parenFocus isSimple focus ++ space re ++ sterms re) False up
  parenFocus isSimple focus = if isSimple then focus else "(" ++ focus ++ ")"
  
  simpleFocus :: Focus a -> Bool
  simpleFocus focus = case focus of
    FName _ -> True
    FTerm term -> simple term
  
  simple term = case term of
    Var _ -> True
    Hole -> True
    U0 -> True
    U1 -> True
    GVar _ -> True
    Quote _ -> True
    Splice e -> simple e
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
  scons cs = case cs of
    [] -> ""
    (Con n ty):cs -> n ++ " : " ++ renderTerm ty ++ "\n" ++ scons cs
  indent s = concat $ intersperse "\n" $ map ("  "++) (lines s)

split :: String -> String -> Char -> [String]
split s acc d = case s of
  [] -> [acc]
  c:cs ->
    if c == d then
      acc : split cs "" d
    else
      split cs (acc ++ [c]) d

loop :: EditorState a -> IO ()
loop state = do
  clearScreen
  -- putStrLn (show $ unCursor state)
  putStrLn (render state)
  s <- getLine
  if s == "q" then
    pure ()
  else do
    state <- case (s, unFocusType state) of
      ("ex", _) -> do
        fn <- getLine
        export state fn
        pure $ Ex state
      ("im", _) -> do
        fn <- getLine
        bs <- B.readFile fn
        let program = runGet getItem bs
        pure $ mkEx program PTop
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
      ("pi", FTTerm) -> pure $ run InsertPi state
      ("u0", FTTerm) -> pure $ run InsertU0 state
      ("u1", FTTerm) -> pure $ run InsertU1 state
      ("code", FTTerm) -> pure $ run InsertCode state
      ("quote", FTTerm) -> pure $ run InsertQuote state
      ("splice", FTTerm) -> pure $ run InsertSplice state
      ('.':s, FTTerm) -> pure $ run (InsertGVar (reverse $ split s "" '.')) state
      ("ns", FTItem) -> pure $ run InsertNamespaceDef state
      ("def", FTItem) -> pure $ run InsertTermDef state
      ("ind", FTItem) -> pure $ run InsertIndDef state
      (_, FTCon) -> pure $ run (InsertCon s) state
      (_, FTTerm) -> pure $ run (InsertVar s) state
      (_, FTName) -> pure $ if s == "" then Ex state else run (SetName s) state
      _ -> pure $ Ex state
    next state
    where
      next :: Ex -> IO ()
      next (Ex state) = loop state

main :: IO ()
main = do
  putStr "\ESC[0m"
  loop (EditorState (Cursor (FItem $ NamespaceDef (Name "main") []) PTop) FTItem)