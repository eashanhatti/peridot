{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Data.Generics.Zipper(Zipper, getHole, setHole, toZipper, fromZipper, query, trans)
import qualified Data.Generics.Zipper as Z
import Surface
import Data.Maybe(fromMaybe)
import Control.Effect.Lift(Lift, Has)
import qualified Control.Effect.Lift as LE
import Control.Carrier.Lift(runM)
import Control.Carrier.State.Strict(runState)
import qualified Control.Effect.State as SE
import Data.Typeable
import Prelude hiding (Left, Right)
import System.IO
import Foreign.C.Types
import Data.Char(chr)
import System.Console.ANSI(clearScreen)
import qualified Elaboration as Elab
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Core as C
import qualified Data.Map as DM
import Elaboration.Error(Error)
import Numeric.Natural
import Data.List(intersperse)
import Data.Maybe(fromJust)
import Data.Typeable(cast, typeOf)
import Data.Data(Data)

data State = State
  { unZipper :: Zipper Item
  , unSide   :: Direction }

data Command
  = Move Direction
  | HardMove Direction
  | InsertTerm Term
  | InsertItem Item
  | Delete
  | Add
  | Quit

type Edit sig m = Has (Lift IO) sig m

(|>) = flip fromMaybe
infixr 1 |>

caseHole :: Zipper a -> (Name -> b) -> (Item -> b) -> (Term -> b) -> ([Item] -> b) -> b
caseHole z nc ic ec lc = query go z where
  go h = case h of
    (cast -> Just i) -> ic i
    (cast -> Just e) -> ec e
    (cast -> Just n) -> nc n
    (cast -> Just l) -> lc l

atomic :: Data a => a -> Bool
atomic f = case f of
  (cast -> Just (Name _)) -> True
  (cast -> Just e) -> case e of
    Hole -> True
    EditorBlank -> True
    Var _ -> True
    GVar _ -> True
    U0 -> True
    U1 -> True
    _ -> False
  (cast -> Just i) -> case i of
    EditorBlankDef -> True
    _ -> False
  _ -> error $ show $ typeOf f

down :: Zipper a -> Zipper a
down z = caseHole z
  (const z)
  (\case
    NamespaceDef _ [] -> fjDown' z
    NamespaceDef _ _ -> fjDownDown z
    TermDef _ _ _ -> fjDown z
    IndDef _ _ [] -> fjDown'Right z
    IndDef _ _ _ -> fjDownDown z
    ProdDef _ _ [] -> fjDown'Right z
    ProdDef _ _ _ -> fjDownDown z)
  undefined
  (\case
    [] -> z
    _ -> fjDownDown z)
  where
    fjDown' = fromJust . Z.down'
    fjDownDown = fromJust . Z.down . fromJust . Z.down
    fjDown = fromJust . Z.down
    fjDown'Right = fromJust . Z.right . fromJust . Z.down'
down' :: Zipper a -> Zipper a
down' z = caseHole z
  (const z)
  (const $ fromJust $ Z.down' z)
  (const $ fromJust $ Z.down' z)
  (\case
    [] -> z
    _ -> fromJust $ Z.down' $ fromJust $ Z.down' $ z)
left :: Zipper a -> Maybe (Zipper a)
left z = Z.left z >>= \z -> caseHole z
  (const $ Just z)
  (const $ Just z)
  (const $ Just z)
  (const $ Z.down z)

right :: Zipper a -> Maybe (Zipper a)
right z = Z.right z >>= \z -> caseHole z
  (const $ Just z)
  (const $ Just z)
  (const $ Just z)
  (const $ Z.down' z)

up :: Zipper a -> Maybe (Zipper a)
up z = Z.up z >>= \z -> caseHole z
  undefined
  (const $ Just z)
  (const $ Just z)
  (const $ Z.up z)

moveLeft :: State -> State
moveLeft (State z d) = case (query atomic z, d) of
  (_, Left) -> case left z of
    Just z -> State z Right
    Nothing -> State (up z |> z) Left
  (True, Right) -> State z Left
  (False, Right) -> State (down z) Right

moveRight :: State -> State
moveRight (State z d) = case (query atomic z, d) of
  (_, Right) -> State (right z |> up z |> z) Right
  (True, Left) -> State z Right
  (False, Left) -> State (down' z) Left

handleInput :: State -> Command -> State
handleInput state@(State z d) cmd = case cmd of
  Move Left -> moveLeft state
  Move Right -> moveRight state
  HardMove Left -> State (left z |> z) d
  HardMove Right -> State (right z |> z) d
  InsertTerm e -> State (setHole e z) d
  InsertItem i -> State (setHole i z) d

parseCommand :: String -> Maybe Command
parseCommand s = case s of
  ";q" -> Just Quit
  "\\" -> Just (InsertTerm $ Lam [Name "_"] Hole)
  "(" -> Just (InsertTerm $ App Hole [Hole])
  " " -> Just Add
  "]" -> Just (Move Right)
  "[" -> Just (Move Left)
  _ -> Nothing 

-- Lol just Ctrl+C + Ctrl+V from StackOverflow. `hSetBuffering stdin NoBuffering` doesn't work on Windows.
getHiddenChar = fmap (chr.fromEnum) c_getch
foreign import ccall unsafe "conio.h getch"
  c_getch :: IO CInt

getCommand :: String -> IO Command
getCommand acc = do
  putStr "\ESC[2K"
  putStr "\ESC[1000D"
  putStr (reverse acc)
  hFlush stdout
  c <- getHiddenChar
  case c of
    '\b' ->
      if null acc then
        pure Delete
      else
        getCommand (tail acc)
    _ -> case parseCommand (reverse $ c:acc) of
      Just cmd -> pure cmd
      Nothing -> getCommand (c:acc)

type Render sig m = Has (SE.State [Error]) sig m

render :: State -> Elab.ElabState -> Item -> (T.Text, [Error])
render state elabState item = (text, errs)
  where
    (errs, text) = SE.run . runState [] $ renderItem item []
    renderItem :: Render sig m => Item -> [String] -> m T.Text
    renderItem item gname = case item of
      TermDef n ty body -> renderTermDef n (GName $ unName n : gname)
      NamespaceDef n items -> combine [greenM "namespace ", pure $ renderName n, indentForced <$> sitems items (unName n : gname)]
      IndDef n ty cons -> renderIndDef n (GName $ unName n : gname)
      ProdDef n _ _ -> renderProdDef n (GName $ unName n : gname)
      EditorFocusDef item side -> case side of
        Left -> combine [yellowM "{", renderItem item gname, yellowM "]"]
        Right -> combine [yellowM "[", renderItem item gname, yellowM "}"]
      EditorBlankDef -> pure "\ESC[7m?\ESC[27m"
    renderTermDef :: Render sig m => Name -> GName -> m T.Text
    renderTermDef name gname =
      let Just (C.TermDef _ def dec) = DM.lookup gname (Elab.globals elabState)
      in combine [greenM "val ", pure $ renderName name, pure " : ", renderTerm dec, pure " = ", indent <$> renderTerm def]
    renderIndDef :: Render sig m => Name -> GName -> m T.Text
    renderIndDef name gname =
      let Just (C.IndDef _ ty (C.IndDefInfo cns)) = DM.lookup gname (Elab.globals elabState)
      in combine [greenM "inductive ", pure $ renderName name, pure " : ", renderTerm ty, indentForced <$> scons cns (unGName gname)]
    renderProdDef :: Render sig m => Name -> GName -> m T.Text
    renderProdDef name gname =
      let Just (C.ProdDef _ ty fields) = DM.lookup gname (Elab.globals elabState)
      in combine [greenM "product ", pure $ renderName name, pure " : ", renderTerm ty, indentForced <$> sfields fields]
    renderTerm :: Render sig m => C.Term -> m T.Text
    renderTerm (C.Term (C.Info side errs) term) = case errs of
      [] -> tterm
      _ -> combine [redM "[", tterm, redM "]"]
      where
        tterm = case side of
          Just Left -> SE.put errs >> combine [yellowM "{", go term, yellowM "]"]
          Just Right -> SE.put errs >> combine [yellowM "[", go term, yellowM "}"]
          Nothing -> go term
        go :: Render sig m => C.TermInner -> m T.Text
        go term = case term of
          C.Var _ ty (C.VarInfo s) -> renderVar ty (T.pack s)
          C.GVar _ ty (C.GVarInfo s') -> renderGName (GName s') ty
          C.TypeType0 -> blueM "U0"
          C.TypeType1 -> blueM "U1"
          C.FunIntro _ _ (C.FunIntroInfo n _) ->
            let (body, params) = goFunIntro term n []
            in combine [greenM "λ", pure params, pure " -> ", renderTerm body]
          C.FunType inTy outTy (C.FunTypeInfo s) -> renderPi s <$> renderTerm inTy <*> renderTerm outTy
          C.FunElim _ _ (C.FunElimInfo n) -> goFunElim term n []
          C.QuoteType term -> combine [blueM "Code ", renderTerm term]
          C.QuoteIntro term _ -> combine [greenM "<", renderTerm term, greenM ">"]
          C.QuoteElim term -> combine [greenM "~", renderTerm term]
          C.ProdType nid args ->
            let Just (GName name) = DM.lookup nid (Elab.idsNames elabState)
            in combine [renderGName (GName name) (C.gen C.TypeType0), pure " ", T.intercalate " " <$> mapM renderTerm args]
          C.ProdIntro ty args -> combine [greenM "#", renderTerm ty, pure $ if null args then "" else " ", T.intercalate " " <$> (mapM renderTerm args)]
          C.IndIntro nid args _ -> combine [
            greenM "#",
            (flip renderGName) (C.gen C.ElabBlank) $ fromJust $ DM.lookup nid (Elab.idsNames elabState),
            pure $ if null args then "" else " ", T.intercalate " " <$> (mapM renderTerm args)]
          C.Meta _ _ -> pure "\ESC[7m?\ESC[27m"
          C.InsertedMeta _ _ _ -> pure "\ESC[7m?\ESC[27m"
          C.ElabError s -> renderSTerm s
          _ -> error $ show term
        goFunIntro :: C.TermInner -> Natural -> [T.Text] -> (C.Term, T.Text)
        goFunIntro (C.FunIntro body _ (C.FunIntroInfo _ s)) n acc = case n of
          1 -> (body, T.intercalate " " $ reverse (renderName s : acc))
          n -> goFunIntro (C.unTerm body) (n - 1) (renderName s : acc)
        goFunElim :: Render sig m => C.TermInner -> Natural -> [C.Term] -> m T.Text
        goFunElim (C.FunElim lam arg _) n args = case n of
          1 -> T.intercalate " " <$> mapM renderTerm (lam:arg:args)
          n -> goFunElim (C.unTerm lam) (n - 1) (arg:args)
    renderVar :: Render sig m => C.Term -> T.Text -> m T.Text
    renderVar term s = case C.unTerm term of
      C.FunType _ outTy _ -> renderVar outTy s
      C.TypeType0 -> pure $ blue s
      C.TypeType1 -> pure $ blue s
      _ -> pure s
    renderGName :: Render sig m => GName -> C.Term -> m T.Text
    renderGName gname@(GName s') ty = case s' of
      [] -> yellowM "{]"
      _ ->
        let
          s = reverse s'
          name = T.pack $ last s
          mpath = init s
          tname = combine [pure $ T.pack $ mconcat $ intersperse "." mpath, pure ".", renderVar ty name]  
        in case gname of
          FocusedGName _ -> combine [yellowM "{", tname, yellowM "]"]
          UnfocusedGName _ -> tname
    renderSTerm :: Render sig m => Term -> m T.Text
    renderSTerm term = case term of
      Var name -> pure $ renderName name
      GVar (GName gname) -> pure $ T.pack $ mconcat $ intersperse "." gname
      Lam names body -> do
        sbody <- renderSTerm body
        pure $ green "λ" <> (T.intercalate " " $ map renderName names) <> " -> " <> sbody
      App lam args -> combine [renderSTerm lam, pure " ", T.intercalate " " <$> mapM renderSTerm args]
      Pi name inTy outTy -> renderPi name <$> renderSTerm inTy <*> renderSTerm outTy
      Let name' def ty body -> do
        let name = renderName name'
        def <- renderSTerm def
        ty <- renderSTerm ty
        body <- renderSTerm body
        pure $ green "let " <> name <> case (multiline ty, multiline def, multiline body) of
          (False, False, False) -> " : " <> ty <> " = " <> def <> inStringSpace <> body
          (False, False, True) -> " : " <> ty <> " = " <> def <> inString <> indent body
          (False, True, False) -> " : " <> ty <> "\n  =" <> indent2 def <> inStringSpace <> body
          (False, True, True) -> " : " <> ty <> "\n  =" <> indent2 def <> inString <> indent body
          (True, False, False) -> "\n  :" <> indent2 ty <> "\n  = " <> def <> inStringSpace <> body
          (True, False, True) -> "\n  :" <> indent2 ty <> "\n  = " <> def <> inString <> indent body
          (True, True, False) -> "\n  :" <> indent2 ty <> "\n  =" <> indent2 def <> inStringSpace <> body
          (True, True, True) -> "\n  :" <> indent2 ty <> "\n  =" <> indent2 def <> inString <> indent body
          where
            inString = green "in"
            inStringSpace = inString <> " "
      U1 -> blueM "U1"
      U0 -> blueM "U0"
      Code term -> combine [blueM "Code ", renderSTerm term]
      Quote term -> combine [greenM "<", renderSTerm term, greenM ">"]
      Splice term -> combine [greenM "~", renderSTerm term]
      MkProd ty args -> combine [greenM "#", renderSTerm ty, pure $ if null args then "" else " ", T.intercalate " " <$> mapM renderSTerm args]
      MkInd name args -> combine [greenM "#", renderGName name (C.gen C.ElabBlank), pure $ if null args then "" else " ", T.intercalate " " <$> mapM renderSTerm args]
      Hole -> pure "\ESC[7m?\ESC[27m"
      EditorBlank -> pure "\ESC[7m?\ESC[27m"
      EditorFocus term side -> case side of
        Left -> combine [yellowM "{", renderSTerm term, yellowM "]"]
        Right -> combine [yellowM "[", renderSTerm term, yellowM "}"]
    renderName :: Name -> T.Text
    renderName name = case name of
      UnfocusedName s -> T.pack s
      FocusedName s Left -> yellow "{" <> T.pack s <> yellow "]"
      FocusedName s Right -> yellow "[" <> T.pack s <> yellow "}"
    renderPi :: Name -> T.Text -> T.Text -> T.Text
    renderPi name inTy outTy = case name of
      FocusedName _ _ -> "(" <> renderName name <> " : " <> inTy <> ") -> " <> outTy
      UnfocusedName "_" -> inTy <> " -> " <> outTy
      UnfocusedName _ -> "(" <> renderName name <> " : " <> inTy <> ") -> " <> outTy

    multiline s = length (T.lines s) /= 1
    scons :: Render sig m => [String] -> [String] -> m T.Text
    scons cns gname = case cns of
      [] -> pure ""
      cn:cns ->
        let Just (C.ConDef _ ty) = DM.lookup (GName $ cn:gname) (Elab.globals elabState)
        in combine [pure $ T.pack cn, pure " : ", renderTerm ty, pure "\n", scons cns gname]
    sfields :: Render sig m => [C.Term] -> m T.Text
    
    sfields fs = mapM renderTerm fs >>= \tfs -> pure $ mconcat $ intersperse "\n" tfs
    sitems :: Render sig m => [Item] -> [String] -> m T.Text
    sitems is gname = case is of
      [] -> pure ""
      [i] -> renderItem i gname
      i:is -> combine [renderItem i gname, pure "\n", sitems is gname]
    combine :: Render sig m => [m T.Text] -> m T.Text
    combine cs = case cs of
      [] -> pure ""
      c:cs -> do
        t <- c
        t' <- combine cs
        pure $ t <> t'

    indent :: T.Text -> T.Text
    indent s =
      if not (multiline s) then
        s
      else
        "\n" <> indentBase s
    indent2 :: T.Text -> T.Text
    indent2 s =
      if not (multiline s) then
        s
      else
        "\n" <> (indentBase . indentBase) s
    indentBase :: T.Text -> T.Text
    indentBase s =
      if not (multiline s) then
        s
      else
        (mconcat $ intersperse "\n" $ map ("  "<>) (T.lines s))
    indentForced :: T.Text -> T.Text
    indentForced s = (if s == "" then "" else "\n") <> (mconcat $ intersperse "\n" $ map ("  "<>) (T.lines s))

red s = "\ESC[31;1m" <> s <> "\ESC[39m"
green s = "\ESC[32;1m" <> s <> "\ESC[39m"
purple s = "\ESC[35;1m" <> s <> "\ESC[39m"
yellow s = "\ESC[33;1m" <> s <> "\ESC[39m"
blue s = "\ESC[36;1m" <> s <> "\ESC[39m"
redM :: Render sig m => T.Text -> m T.Text
redM = pure . red
greenM :: Render sig m => T.Text -> m T.Text
greenM = pure . green
purpleM :: Render sig m => T.Text -> m T.Text
purpleM = pure . purple
yellowM :: Render sig m => T.Text -> m T.Text
yellowM = pure . yellow
blueM :: Render sig m => T.Text -> m T.Text
blueM = pure . blue

insertFocusMarker :: Data a => Direction -> a -> a
insertFocusMarker d f = case f of
  (cast -> Just i) -> fromJust $ cast (EditorFocusDef i d)
  (cast -> Just e) -> fromJust $ cast (EditorFocus e d)
  (cast -> Just (Name n)) -> fromJust $ cast (FocusedName n d)
  _ -> f
-- case cast f :: Maybe Item of
--   Just i -> fromJust $ cast (EditorFocusDef i d)
--   Nothing -> case cast f :: Maybe Term of
--     Just e -> fromJust $ cast (EditorFocus e d)
--     Nothing -> case cast f :: Maybe Name of
--       Just (Name n) -> fromJust $ cast (FocusedName n)
--       Nothing -> f

loop :: Edit sig m => State -> m ()
loop state@(State z d) = do
  LE.sendIO $ clearScreen
  let item = fromZipper (trans (insertFocusMarker d) z)
  LE.sendIO $ putStrLn $ show d
  LE.sendIO $ putStrLn $ show $ query typeOf z
  let (cTerm, elabState) = Elab.elabFresh item
  let (s, es) = render state elabState item
  LE.sendIO $ TIO.putStrLn (s <> "\n")
  cmd <- LE.sendIO $ getCommand ""
  case cmd of
    Quit -> pure ()
    _ -> loop (handleInput state cmd)

main :: IO ()
main = do
  putStr "\ESC[0;75;\"{MOVELEFT}\"p"
  putStr "\ESC[0;77;\"{MOVERIGHT}\"p"
  runM @IO $ loop (State (toZipper $ NamespaceDef (Name "main") []) Left)