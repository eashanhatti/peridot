{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

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
import qualified Data.Map as DM
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.ByteString.Lazy as LB
import Data.Maybe(fromJust)
import Data.List(intersperse)
import Prelude hiding (Left, Right)
import Parsing(getItem)
import System.IO
import GHC.IO.Encoding
import Data.Char
import Foreign.C.Types
import Data.Bifunctor
import Control.Monad(forM_)
import Control.Effect.State(State)
import qualified Control.Effect.State as SE
import Control.Effect.Lift(Lift, Has)
import qualified Control.Effect.Lift as LE
import Control.Carrier.State.Strict(runState)
import Control.Carrier.Lift(runM)
import qualified Elaboration as Elab
import qualified Core as C
import Debug.Trace(traceShowId)
import Numeric.Natural
import Elaboration.Error
import System.IO.Unsafe
import Data.IORef
import Etc

data Con = Con String Term | EditorBlankCon
  deriving (Show, Eq)

unCon (Con n t) = (n, t)
conPair (n, t) = Con n t

data Path a where
  PTop                 :: Path Item
  PTermDefName         :: Path Item -> Term -> Term -> Path Name
  PTermDefBody         :: Path Item -> String -> Term -> Path Term
  PTermDefTy           :: Path Item -> String -> Term -> Path Term
  PNamespaceDefName    :: Path Item -> [Item] -> Path Name
  PNamespaceDefItems   :: Path Item -> String -> [Item] -> [Item] -> Path Item
  PIndDefName          :: Path Item -> Term -> [Con] -> Path Name
  PIndDefTy            :: Path Item -> String -> [Con] -> Path Term
  PIndDefCons          :: Path Item -> String -> Term -> [Con] -> [Con] -> Path Con
  PConName             :: Path Con  -> Term -> Path Name
  PConTy               :: Path Con  -> String -> Path Term
  PProdDefName         :: Path Item -> Term -> [Term] -> Path Name
  PProdDefTy           :: Path Item -> String -> [Term] -> Path Term
  PProdDefFields       :: Path Item -> String -> Term -> [Term] -> [Term] -> Path Term
  PLamParams           :: Path Term -> [String] -> [String] -> Term -> Path Name
  PLamBody             :: Path Term -> [String] -> Path Term
  PAppTerms            :: Path Term -> [Term] -> [Term] -> Path Term
  PLetName             :: Path Term -> Term -> Term -> Term -> Path Name
  PLetDefTy            :: Path Term -> String -> Term -> Term -> Path Term
  PLetDef              :: Path Term -> String -> Term -> Term -> Path Term
  PLetBody             :: Path Term -> String -> Term -> Term -> Path Term
  PMkProdTy            :: Path Term -> [Term] -> Path Term
  PMkProdArgs          :: Path Term -> Term -> [Term] -> [Term] -> Path Term
  PMkIndName           :: Path Term -> [Term] -> Path GName
  PMkIndArgs           :: Path Term -> GName -> [Term] -> [Term] -> Path Term
  PPiName              :: Path Term -> Term -> Term -> Path Name
  PPiIn                :: Path Term -> String -> Term -> Path Term
  PPiOut               :: Path Term -> String -> Term -> Path Term
  PMatchScr            :: Path Term -> [Term] -> [Term] -> [Clause] -> Path Term
  PMatchClause         :: Path Term -> [Term] -> [Clause] -> [Clause] -> Path Clause
  PMatchClausePat      :: Path Clause -> Term -> Path Pattern
  PMatchClauseBody     :: Path Clause -> Pattern -> Path Term
  PPatConName          :: Path Pattern -> [Pattern] -> Path GName
  PPatConArg           :: Path Pattern -> GName -> [Pattern] -> [Pattern] -> Path Pattern
  PCode                :: Path Term -> Path Term
  PQuote               :: Path Term -> Path Term
  PSplice              :: Path Term -> Path Term
deriving instance Show (Path a)
deriving instance Eq (Path a)

data Focus a where
  FName   :: Name -> Focus Name
  FTerm   :: Term -> Focus Term
  FItem   :: Item -> Focus Item
  FGName  :: GName -> Focus GName
  FClause :: Clause -> Focus Clause
  FCon    :: Con -> Focus Con
  FPat    :: Pattern -> Focus Pattern
deriving instance Show (Focus a)
deriving instance Eq (Focus a)

unFNameS :: Focus Name -> String
unFNameS (FName (Name s)) = s
unFName :: Focus Name -> Name
unFName (FName n) = n
unFGName :: Focus GName -> GName
unFGName (FGName n) = n
unFTerm :: Focus Term -> Term
unFTerm (FTerm e) = e
unFItem :: Focus Item -> Item
unFItem (FItem i) = i
unFCon :: Focus Con -> Con
unFCon  (FCon c) = c
unFClause :: Focus Clause -> Clause
unFClause (FClause c) = c
unFPat :: Focus Pattern -> Pattern
unFPat (FPat p) = p

data FocusType a where
  FTName   :: FocusType Name
  FTTerm   :: FocusType Term
  FTItem   :: FocusType Item
  FTCon    :: FocusType Con
  FTGName  :: FocusType GName
  FTClause :: FocusType Clause
  FTPat    :: FocusType Pattern
deriving instance Eq (FocusType a)
deriving instance Show (FocusType a)

data Cursor a = Cursor { unFocus :: Focus a, unPath :: Path a }
deriving instance Show (Cursor a)
deriving instance Eq (Cursor a)

data EditorState a = EditorState { unCursor :: Cursor a, unFocusType :: FocusType a, unSide :: Direction }
deriving instance Eq (EditorState a)
deriving instance Show (EditorState a)

statesEq :: EditorState a -> EditorState b -> Bool
statesEq st st' = case (unFocusType st, unFocusType st') of
  (FTName, FTName) -> st == st'
  (FTTerm, FTTerm) -> st == st'
  (FTItem, FTItem) -> st == st'
  (FTCon, FTCon) -> st == st'
  (FTGName, FTGName) -> st == st'
  (FTClause, FTClause) -> st == st'
  (FTPat, FTPat) -> st == st'
  _ -> False

data Ex = forall a. Ex { unEx :: EditorState a }

type Edit sig m = (Has (State Changes) sig m, Has (State GName) sig m, Has (State (Maybe ItemPart)) sig m)
type EditIO sig m = (Has (Lift IO) sig m, Edit sig m)

data Command a where
  InsertTerm         :: TermInsertionType -> Command Term
  InsertVar          :: String -> Command Term
  InsertHole         :: Command Term
  InsertU0           :: Command Term
  InsertU1           :: Command Term
  InsertTermDef      :: Command Item
  InsertNamespaceDef :: Command Item
  InsertIndDef       :: Command Item
  InsertProdDef      :: Command Item
  InsertGVar         :: [String] -> Command Term
  InsertCon          :: String -> Command Con
  SetName            :: String -> Command Name
  SetGName           :: [String] -> Command GName
  MoveOut            :: Direction -> Command a
  MoveRight          :: Command a
  MoveLeft           :: Command a
  MoveInLeft         :: Command a
  MoveInRight        :: Command a
  Add                :: Command a
  Delete             :: Command a

class MkFT a where focusType :: FocusType a
instance MkFT Term where    focusType = FTTerm
instance MkFT Name where    focusType = FTName
instance MkFT Item where    focusType = FTItem
instance MkFT Con where     focusType = FTCon
instance MkFT GName where   focusType = FTGName
instance MkFT Clause where  focusType = FTClause
instance MkFT Pattern where focusType = FTPat

class MkFocus a where focus :: a -> Focus a
instance MkFocus Term where    focus = FTerm
instance MkFocus Item where    focus = FItem
instance MkFocus Name where    focus = FName
instance MkFocus Con where     focus = FCon
instance MkFocus GName where   focus = FGName
instance MkFocus Clause where  focus = FClause
instance MkFocus Pattern where focus = FPat

type Changes = DM.Map GName ItemPart

mkEx :: (MkFT a, MkFocus a) => a -> Path a -> Direction -> Ex
mkEx f p s = Ex $ EditorState (Cursor (focus f) p) focusType s

mkExE :: (MkFT a, MkFocus a, Edit sig m) => a -> Path a -> Direction -> m Ex
mkExE f p s = pure $ mkEx f p s

blankFocus :: Focus a -> Bool
blankFocus focus = case focus of
  FTerm EditorBlank -> True
  FItem EditorBlankDef -> True
  FName (Name "") -> True
  FGName (GName []) -> True
  FCon EditorBlankCon -> True
  FClause EditorBlankClause -> True
  FPat EditorBlankPat -> True
  _ -> False

popName :: Has (State GName) sig m => m ()
popName = do
  gname <- SE.get
  SE.put (GName $ tail $ unGName gname)

pushName :: Has (State GName) sig m => String -> m ()
pushName n = do
  gname <- SE.get
  SE.put (GName $ n : unGName gname)

putPart :: Has (State (Maybe ItemPart)) sig m => ItemPart -> m ()
putPart part = SE.put @(Maybe ItemPart) (Just part)

clearPart :: Has (State (Maybe ItemPart)) sig m => m ()
clearPart = SE.put @(Maybe ItemPart) Nothing

markChange :: Edit sig m => m ()
markChange = do
  part <- SE.get @(Maybe ItemPart)
  case part of
    Just part -> do
      changes <- SE.get @Changes
      name <- SE.get @GName
      case DM.lookup name changes of
        Just Dec -> pure ()
        _ -> SE.put @Changes (DM.insert name part changes)
    Nothing -> pure ()

itemName :: Path a -> Focus a -> Maybe String
itemName path focus = case path of
  PTermDefName _ _ _ -> Just $ unFNameS focus
  PTermDefBody _ name _ -> Just name
  PTermDefTy _ name _ -> Just name
  PNamespaceDefName _ _ -> Just $ unFNameS focus
  PNamespaceDefItems _ name _ _ -> Just name
  PIndDefName _ _ _ -> Just $ unFNameS focus
  PIndDefTy _ name _ -> Just name
  PIndDefCons _ name _ _ _ -> Just name
  PConName _ _ -> Just $ unFNameS focus
  PConTy _ name -> Just name
  PProdDefName _ _ _ -> Just $ unFNameS focus
  PProdDefTy _ name _ -> Just name
  PProdDefFields _ name _ _ _ -> Just name
  _ -> Nothing

run :: Edit sig m => Command a -> EditorState a -> m Ex
run command state@(EditorState (Cursor focus path) focusType side) = do
  state' <- case command of
    InsertTerm ti -> do
      markChange
      case ti of
        TILam -> mkExE (Lam [Name "_"] termFocus) path Left
        TIApp -> mkExE (App termFocus [Hole]) path Left
        TILet -> mkExE (Let (Name "_") Hole Hole termFocus) path Left
        TIPi -> mkExE (Pi (Name "_") termFocus Hole) path Left
        TICode -> mkExE (Code termFocus) path Left
        TIQuote -> mkExE (Quote termFocus) path Left
        TISplice -> mkExE (Splice termFocus) path Left
        TIMkProd -> mkExE (MkProd termFocus []) path Left
        TIMkInd -> mkExE (MkInd (GName []) []) path Left -- FIXME: `GName []`
      where
        termFocus = unFTerm focus
    InsertVar s -> markChange >> mkExE (Var (Name s)) path Left
    InsertHole -> markChange >> mkExE Hole path Left
    InsertTermDef -> markItemInsertion >> mkExE (TermDef (Name "_") Hole Hole) path Left
    InsertNamespaceDef -> mkExE (NamespaceDef (Name "_") []) path Left
    InsertIndDef -> markItemInsertion >> mkExE (IndDef (Name "_") Hole []) path Left
    InsertU0 -> markChange >> mkExE U0 path Left
    InsertU1 -> markChange >> mkExE U1 path Left
    InsertGVar ns -> markChange >> mkExE (GVar $ GName ns) path Left
    InsertCon s -> markItemInsertion >> mkExE Hole (PConTy path s) Left
    InsertProdDef -> markItemInsertion >> mkExE (ProdDef (Name "_") Hole []) path Left
    SetName s -> do
      case itemName path focus of
        Just _ -> do
          part <- SE.get @(Maybe ItemPart)
          putPart Dec
          markChange
          case part of
            Just part -> putPart part
            Nothing -> clearPart
          popName
          pushName s
        Nothing -> pure ()
      mkExE (Name s) path Left
    SetGName ns -> markChange >>= pure (mkExE (GName ns) path Left)
    Add ->
      if blankFocus focus then
        pure oldState
      else case path of
        PLamParams up ln rn body -> mkExE (Name "") (PLamParams up (insertNameR focus ln) rn body) Left
        PAppTerms up le re -> mkExE EditorBlank (PAppTerms up (insertFocusR focus le) re) Left
        PNamespaceDefItems up name li ri -> mkExE EditorBlankDef (PNamespaceDefItems up name (insertFocusR focus li) ri) Left
        PIndDefCons up name ty lc rc -> mkExE EditorBlankCon (PIndDefCons up name ty (insertFocusR focus lc) rc) Left
        PProdDefFields up name ty lf rf -> mkExE EditorBlank (PProdDefFields up name ty (insertFocusR focus lf) rf) Left
        PMkProdArgs up ty le re -> mkExE EditorBlank (PMkProdArgs up ty (insertFocusR focus le) re) Left
        PMatchScr up ls rs cs -> mkExE EditorBlank (PMatchScr up (insertFocusR focus ls) rs cs) Left
        PMatchClause up ss rc lc -> mkExE EditorBlankClause (PMatchClause up ss (insertFocusR focus rc) lc) Left
        _ -> pure oldState
    MoveRight -> case path of
      PTop -> pure sideRight
      PLamParams up ln [] body -> mkExE body (PLamBody up (insertNameR focus ln)) Left
      PLamParams up ln (n:rn) body -> mkExE (Name n) (PLamParams up (insertNameR focus ln) rn body) Left
      PLamBody up ns -> pure sideRight
      PAppTerms up le [] -> pure sideRight
      PAppTerms up le (r:re) -> mkExE r (PAppTerms up (insertFocusR focus le) re) Left
      PLetName up def defTy body -> mkExE defTy (PLetDefTy up (unFNameS focus) def body) Left
      PLetDefTy up name def body -> mkExE def (PLetDef up name (unFTerm focus) body) Left
      PLetDef up name defTy body -> mkExE body (PLetBody up name (unFTerm focus) defTy) Left
      PMkProdTy up [] -> mkExE EditorBlank (PMkProdArgs up (unFTerm focus) [] []) Left
      PMkProdTy up (e:es) -> mkExE e (PMkProdArgs up (unFTerm focus) [] es) Left
      PMkProdArgs up ty le [] -> pure sideRight
      PMkProdArgs up ty le (r:re) -> mkExE r (PMkProdArgs up ty (insertFocusR focus le) re) Left
      PMkIndName up [] -> mkExE EditorBlank (PMkIndArgs up (unFGName focus) [] []) Left
      PMkIndName up (e:es) -> mkExE e (PMkIndArgs up (unFGName focus) [] es) Left
      PMkIndArgs up ty le [] -> pure sideRight
      PMkIndArgs up ty le (r:re) -> mkExE r (PMkIndArgs up ty (insertFocusR focus le) re) Left
      PLetBody _ _ _ _ -> pure sideRight
      PTermDefName up ty body -> putPart Dec >> mkExE ty (PTermDefTy up (unFNameS focus) body) Left
      PTermDefTy up name body -> putPart Def >> mkExE body (PTermDefBody up name (unFTerm focus)) Left
      PTermDefBody _ _ _ -> pure sideRight
      PNamespaceDefName up [] -> mkExE EditorBlankDef (PNamespaceDefItems up (unFNameS focus) [] []) Left
      PNamespaceDefName up (i:is) -> mkExE i (PNamespaceDefItems up (unFNameS focus) [] is) Left
      PNamespaceDefItems up name _ [] -> pure sideRight
      PNamespaceDefItems up name li (i:ri) -> mkExE i (PNamespaceDefItems up name (insertFocusR focus li) ri) Left
      PPiName up inTy outTy -> mkExE inTy (PPiIn up (unFNameS focus) outTy) Left
      PPiIn up name outTy -> mkExE outTy (PPiOut up name (unFTerm focus)) Left
      PPiOut _ _ _ -> pure sideRight
      PCode _ -> pure sideRight
      PQuote _ -> pure sideRight
      PSplice _ -> pure sideRight
      PIndDefName up ty cons -> putPart Dec >> mkExE ty (PIndDefTy up (unFNameS focus) cons) Left
      PIndDefTy up name [] -> clearPart >> mkExE EditorBlankCon (PIndDefCons up name (unFTerm focus) [] []) Left 
      PIndDefTy up name (c:cs) -> clearPart >> mkExE c (PIndDefCons up name (unFTerm focus) [] cs) Left
      PIndDefCons up name ty lc [] -> pure sideRight
      PIndDefCons up name ty lc (c:rc) -> mkExE c (PIndDefCons up name ty (insertFocusR focus lc) rc) Left
      PProdDefName up ty fs -> putPart Dec >> mkExE ty (PProdDefTy up (unFNameS focus) fs) Left
      PProdDefTy up name [] -> clearPart >> mkExE EditorBlank (PProdDefFields up name (unFTerm focus) [] []) Left
      PProdDefTy up name (f:fs) -> clearPart >> mkExE f (PProdDefFields up name (unFTerm focus) [] fs) Left
      PProdDefFields up name ty lf [] -> pure sideRight
      PProdDefFields up name ty lf (f:rf) -> mkExE f (PProdDefFields up name ty (insertFocusR focus lf) rf) Left
      PConName up ty -> putPart Dec >> mkExE ty (PConTy up (unFNameS focus)) Left
      PConTy _ _ -> clearPart >> pure sideRight
      PMatchScr up ls [] [] -> mkExE EditorBlankClause (PMatchClause up (insertFocusR focus ls) [] []) Left
      PMatchScr up ls [] (c:cs) -> mkExE c (PMatchClause up (insertFocusR focus ls) [] cs) Left
      PMatchScr up ls (s:rs) cs -> mkExE s (PMatchScr up (insertFocusR focus ls) rs cs) Left
      PMatchClause up ss lc [] -> pure sideRight
      PMatchClause up ss lc (c:rc) -> mkExE c (PMatchClause up ss (insertFocusR focus lc) rc) Left
      PMatchClausePat up body -> mkExE body (PMatchClauseBody up (unFPat focus)) Left
      PMatchClauseBody up pat -> pure sideRight
      PPatConName up [] -> mkExE EditorBlankPat (PPatConArg up (unFGName focus) [] []) Left
      PPatConArg up name lp [] -> pure sideRight
      PPatConArg up name lp (p:rp) -> mkExE p (PPatConArg up name (insertFocusR focus lp) rp) Left
    MoveLeft -> case path of
      PTop -> pure sideLeft
      PLamParams up [] rn body -> orSideLeft $ mkExE (Name "") (PLamParams up [] (insertNameL focus rn) body) Left
      PLamParams up ln rn body -> mkExE (Name $ last ln) (PLamParams up (init ln) (insertNameL focus rn) body) Left
      PLamBody up ns -> mkExE (Name $ last ns) (PLamParams up (init ns) [] (unFTerm focus)) Left
      PAppTerms up [] re -> orSideLeft $ mkExE EditorBlank (PAppTerms up [] (insertFocusL focus re)) Right
      PAppTerms up le re -> mkExE (last le) (PAppTerms up (init le) (insertFocusL focus re)) Right
      PLetName _ _ _ _ -> pure sideLeft
      PLetDefTy up name def body -> mkExE (Name name) (PLetName up def (unFTerm focus) body) Left
      PLetDef up name defTy body -> mkExE defTy (PLetDefTy up name (unFTerm focus) body) Right
      PLetBody up name def defTy -> mkExE def (PLetDef up name defTy (unFTerm focus)) Right
      PMkProdTy _ _ -> pure sideLeft
      PMkProdArgs up ty [] es -> mkExE ty (PMkProdTy up es) Right
      PMkProdArgs up ty le re -> mkExE (last le) (PMkProdArgs up ty (init le) (insertFocusL focus re)) Right
      PMkIndName _ _ -> pure sideLeft
      PMkIndArgs up name [] es -> mkExE name (PMkIndName up es) Right
      PMkIndArgs up name le re -> mkExE (last le) (PMkIndArgs up name (init le) (insertFocusL focus re)) Right
      PTermDefName up ty body -> pure sideLeft
      PTermDefTy up name body -> clearPart >> mkExE (Name name) (PTermDefName up (unFTerm focus) body) Left
      PTermDefBody up name ty -> putPart Dec >> mkExE ty (PTermDefTy up name (unFTerm focus)) Right
      PNamespaceDefName up _ -> pure sideLeft
      PNamespaceDefItems up name [] ri -> orSideLeft $ mkExE EditorBlankDef (PNamespaceDefItems up name [] (insertFocusL focus ri)) Right
      PNamespaceDefItems up name li ri -> mkExE (last li) (PNamespaceDefItems up name (init li) (insertFocusL focus ri)) Right
      PPiName _ _ _ -> pure sideLeft
      PPiIn up name outTy -> mkExE (Name name) (PPiName up (unFTerm focus) outTy) Left
      PPiOut up name inTy -> mkExE inTy (PPiIn up name (unFTerm focus)) Right
      PCode _ -> pure sideLeft
      PQuote _ -> pure sideLeft
      PSplice _ -> pure sideLeft
      PIndDefName _ _ _ -> pure sideLeft
      PIndDefTy up name cons -> clearPart >> mkExE (Name name) (PIndDefName up (unFTerm focus) cons) Left
      PIndDefCons up name ty [] rc -> orSideLeft $ mkExE EditorBlankCon (PIndDefCons up name ty [] (insertFocusL focus rc)) Right
      PIndDefCons up name ty lc rc -> mkExE (last lc) (PIndDefCons up name ty (init lc) (insertFocusL focus rc)) Right
      PProdDefName _ _ _ -> pure sideLeft
      PProdDefTy up name fs -> mkExE (Name name) (PProdDefName up (unFTerm focus) fs) Left
      PProdDefFields up name ty [] rf -> orSideLeft $ mkExE EditorBlank (PProdDefFields up name ty [] (insertFocusL focus rf)) Right
      PProdDefFields up name ty lf rf -> mkExE (last lf) (PProdDefFields up name ty (init lf) (insertFocusL focus rf)) Right
      PConName _ _ -> pure sideLeft
      PConTy up name -> clearPart >> mkExE (Name name) (PConName up (unFTerm focus)) Left
      PMatchScr up [] rs cs -> orSideLeft $ mkExE EditorBlank (PMatchScr up [] (insertFocusL focus rs) cs) Right
      PMatchScr up ls rs cs -> mkExE (last ls) (PMatchScr up (init ls) (insertFocusL focus rs) cs) Right
      PMatchClause up ss [] rc -> orSideLeft $ mkExE EditorBlankClause (PMatchClause up ss [] (insertFocusL focus rc)) Right
      PMatchClausePat _ _ -> pure sideLeft
      PMatchClauseBody up pat -> mkExE pat (PMatchClausePat up (unFTerm focus)) Right
      PPatConName _ _ -> pure sideLeft
      PPatConArg up name [] rp -> mkExE name (PPatConName up (insertFocusL focus rp)) Right
      PPatConArg up name lp rp -> mkExE (last lp) (PPatConArg up name (init lp) (insertFocusL focus rp)) Right
      where
        orSideLeft :: Edit sig m => m Ex -> m Ex
        orSideLeft ex =
          if blankFocus focus then
            pure sideLeft
          else
            ex
    MoveOut d -> do
      case itemName path focus of
        Just _ -> popName
        Nothing -> pure ()
      case path of
        PTop -> pure oldState
        PLamParams up ln rn body -> mkExE (Lam (map Name ln ++ [unFName focus] ++ map Name rn) body) up d
        PLamBody up ns -> mkExE (Lam (map Name ns) (unFTerm focus)) up d
        PAppTerms up le re ->
          let es = le ++ insertFocusL focus re
          in mkExE (App (head es) (tail es)) up d
        PLetName up def defTy body -> mkExE (Let (unFName focus) def defTy body) up d
        PLetDefTy up name def body -> mkExE (Let (Name name) def (unFTerm focus) body) up d
        PLetDef up name defTy body -> mkExE (Let (Name name) (unFTerm focus) defTy body) up d
        PLetBody up name def defTy -> mkExE (Let (Name name) def defTy (unFTerm focus)) up d
        PMkProdTy up es -> mkExE (MkProd (unFTerm focus) es) up d
        PMkProdArgs up ty le re -> mkExE (MkProd ty (le ++ insertFocusL focus re)) up d
        PMkIndName up es -> mkExE (MkInd (unFGName focus) es) up d
        PMkIndArgs up name le re -> mkExE (MkInd name (le ++ insertFocusL focus re)) up d
        PTermDefName up ty body -> mkExE (TermDef (unFName focus) ty body) up d
        PTermDefTy up name body -> clearPart >> mkExE (TermDef (Name name) (unFTerm focus) body) up d
        PTermDefBody up name ty -> clearPart >> mkExE (TermDef (Name name) ty (unFTerm focus)) up d
        PNamespaceDefName up items -> mkExE (NamespaceDef (unFName focus) items) up d
        PNamespaceDefItems up name li ri -> mkExE (NamespaceDef (Name name) (li ++ insertFocusL focus ri)) up d
        PPiName up inTy outTy -> mkExE (Pi (unFName focus) inTy outTy) up d
        PPiIn up name outTy -> mkExE (Pi (Name name) (unFTerm focus) outTy) up d
        PPiOut up name inTy -> mkExE (Pi (Name name) inTy (unFTerm focus)) up d
        PCode up -> mkExE (Code $ unFTerm focus) up d
        PQuote up -> mkExE (Quote $ unFTerm focus) up d
        PSplice up -> mkExE (Splice $ unFTerm focus) up d
        PIndDefName up ty cons -> mkExE (IndDef (unFName focus) ty (map (first Name . unCon) cons)) up d
        PIndDefCons up name ty lc [] -> case unFCon focus of
          Con n t -> mkExE (IndDef (Name name) ty (map (first Name . unCon) lc ++ [(Name n, t)])) up d
          EditorBlankCon -> mkExE (IndDef (Name name) ty []) up d
        PIndDefTy up name cons -> clearPart >> mkExE (IndDef (Name name) (unFTerm focus) (map (first Name . unCon) cons)) up d
        PIndDefCons up name ty lc rc -> mkExE (IndDef (Name name) ty (map (first Name . unCon) $ lc ++ insertFocusL focus rc)) up d
        PProdDefName up ty fs -> mkExE (ProdDef (unFName focus) ty fs) up d
        PProdDefTy up name fs -> clearPart >> mkExE (ProdDef (Name name) (unFTerm focus) fs) up d
        PProdDefFields up name ty lf rf -> mkExE (ProdDef (Name name) ty (lf ++ insertFocusL focus rf)) up d
        PConName up ty -> mkExE (Con (unFNameS focus) ty) up d
        PConTy up name -> clearPart >> mkExE (Con name (unFTerm focus)) up d
        PMatchScr up ls rs cs -> mkExE (Match (ls ++ insertFocusL focus rs) cs) up d
        PMatchClause up ss lc rc -> mkExE (Match ss (lc ++ insertFocusL focus rc)) up d
        PMatchClausePat up body -> mkExE (Clause (unFPat focus) body) up d
        PMatchClauseBody up pat -> mkExE (Clause pat (unFTerm focus)) up d
        PPatConName up ps -> mkExE (ConPat (unFGName focus) ps) up d
        PPatConArg up name lp rp -> mkExE (ConPat name (lp ++ insertFocusL focus rp)) up d
    MoveInLeft -> case focus of
      FTerm focus -> case focus of
        Lam (n:ns) body -> mkExE n (PLamParams path [] (map unName ns) body) Left
        App lam args -> mkExE lam (PAppTerms path [] args) Left
        Let name def defTy body -> mkExE name (PLetName path def defTy body) Left
        Pi name inTy outTy -> mkExE name (PPiName path inTy outTy) Left
        Var _ -> pure oldState
        GVar _ -> pure oldState
        U0 -> pure oldState
        U1 -> pure oldState
        Code ty -> mkExE ty (PCode path) Left
        Quote e -> mkExE e (PQuote path) Left
        Splice e -> mkExE e (PSplice path) Left
        MkProd ty es -> mkExE ty (PMkProdTy path es) Left
        MkInd name es -> mkExE name (PMkIndName path es) Left
        Match (s:ss) cs -> mkExE s (PMatchScr path [] ss cs) Left
        Match [] cs -> mkExE EditorBlank (PMatchScr path [] [] cs) Left
        Hole -> pure oldState
        EditorBlank -> pure oldState
      FItem focus -> do
        let
          (n, ex) = case focus of
            TermDef name@(Name n) ty body -> (n, mkExE name (PTermDefName path ty body) Left)
            NamespaceDef name@(Name n) items -> (n, mkExE name (PNamespaceDefName path items) Left)
            IndDef name@(Name n) ty cons -> (n, mkExE name (PIndDefName path ty (map (conPair . first unName) cons)) Left)
            ProdDef name@(Name n) ty fields -> (n, mkExE name (PProdDefName path ty fields) Left)
        pushName n
        ex
      FCon focus -> case focus of
        Con n t -> do
          pushName n
          mkExE (Name n) (PConName path t) Left
        EditorBlankCon -> pure sideLeft
      FName _ -> pure sideLeft
      FClause (Clause p b) -> mkExE p (PMatchClausePat path b) Left
      FPat (ConPat name ps) -> mkExE name (PPatConName path ps) Left
      FPat _ -> pure oldState
    MoveInRight -> case focus of
      FTerm focus -> case focus of
        Lam ns body -> mkExE body (PLamBody path (map unName ns)) Right
        App lam args -> mkExE (last args) (PAppTerms path (lam : init args) []) Right
        Let (Name name) def defTy body -> mkExE body (PLetBody path name def defTy) Right
        Pi (Name name) inTy outTy -> mkExE outTy (PPiOut path name inTy) Right
        Var _ -> pure oldState
        GVar _ -> pure oldState
        U0 -> pure oldState
        U1 -> pure oldState
        Code ty -> mkExE ty (PCode path) Right
        Quote e -> mkExE e (PQuote path) Right
        Splice e -> mkExE e (PSplice path) Right
        MkProd ty es -> mkExE EditorBlank (PMkProdArgs path ty es []) Right
        MkInd name es -> mkExE EditorBlank (PMkIndArgs path name es []) Right
        Match ss cs -> mkExE EditorBlankClause (PMatchClause path ss cs []) Right
        Hole -> pure oldState
        EditorBlank -> pure oldState
      FItem focus -> do
        let
          (n, ex) = case focus of
            TermDef (Name n) ty body -> (n, putPart Def >> mkExE body (PTermDefBody path n ty) Right)
            NamespaceDef (Name n) [] -> (n, mkExE EditorBlankDef (PNamespaceDefItems path n [] []) Right)
            NamespaceDef (Name n) items -> (n, mkExE (last items) (PNamespaceDefItems path n (init items) []) Right)
            IndDef (Name n) ty [] -> (n, mkExE EditorBlankCon (PIndDefCons path n ty [] []) Right)
            IndDef (Name n) ty cons -> (n, mkExE ((\(Name n, t) -> Con n t) $ last cons) (PIndDefCons path n ty (map (conPair . first unName) $ init cons) []) Right)
            ProdDef (Name n) ty [] -> (n, mkExE EditorBlank (PProdDefFields path n ty [] []) Right)
            ProdDef (Name n) ty fs -> (n, mkExE (last fs) (PProdDefFields path n ty (init fs) []) Right)
        pushName n
        ex
      FCon focus -> case focus of
        Con n t -> do
          pushName n
          mkExE t (PConTy path n) Right
        EditorBlankCon -> pure sideRight
      FName _ -> pure sideRight
      FClause (Clause p b) -> mkExE b (PMatchClauseBody path p) Right
      FPat (ConPat name ps) -> mkExE EditorBlankPat (PPatConArg path name ps []) Right
      FPat _ -> pure oldState
    Delete -> case path of
      PNamespaceDefItems up name [] []       -> mkExE (Name name) (PNamespaceDefName up []) Left
      PNamespaceDefItems up name li@(_:_) ri -> mkExE (last li) (PNamespaceDefItems up name (init li) ri) Right
      PIndDefCons up name ty [] []           -> markDecChange >> mkExE ty (PIndDefTy up name []) Right
      PIndDefCons up name ty lc@(_:_) rc     -> markDecChange >> mkExE (last lc) (PIndDefCons up name ty (init lc) rc) Right
      PLamParams up [] [] body               -> pure oldState
      PLamParams up [] (n:rn) body           -> markChange >> mkExE (Name n) (PLamParams up [] rn body) Left
      PLamParams up ln rn body               -> markChange >> mkExE (Name $ last ln) (PLamParams up (init ln) rn body) Right
      PProdDefFields up name ty [] []        -> mkExE ty (PProdDefTy up name []) Right
      PProdDefFields up name ty lf@(_:_) rf  -> mkExE (last lf) (PProdDefFields up name ty (init lf) rf) Right
      PMkProdArgs up ty [] []                -> markChange >> mkExE ty path Right
      PMkProdArgs up ty le@(_:_) re          -> markChange >> mkExE (last le) (PMkProdArgs up ty (init le) re) Right
      PAppTerms up le re -> markChange >> case le ++ re of
        [] -> mkExE Hole path Right
        [e] -> mkExE e path Right
        _ -> mkExE (last le) (PAppTerms up (init le) re) Right
      _ -> case focusType of
        FTTerm -> markChange >> mkExE Hole path Left
        _ -> pure oldState
  pure state'
  where
    oldState = Ex state
    sideRight = case side of
      Left -> Ex $ state { unSide = Right }
      Right -> Ex state
    sideLeft = case side of
      Left -> Ex state
      Right -> Ex $ state { unSide = Left }
    insertFocusR :: Focus a -> [a] -> [a]
    insertFocusR focus la = case focus of
      FTerm EditorBlank -> la
      FTerm e -> la ++ [e]
      FCon EditorBlankCon -> la
      FCon c -> la ++ [c]
      FItem EditorBlankDef -> la
      FItem i -> la ++ [i]
      FClause EditorBlankClause -> la
      FClause c -> la ++ [c]
      FPat EditorBlankPat -> la
      FPat p -> la ++ [p]
    insertFocusL :: Focus a -> [a] -> [a]
    insertFocusL focus la = case focus of
      FTerm EditorBlank -> la
      FTerm e -> e:la
      FCon EditorBlankCon -> la
      FCon c -> c:la
      FItem EditorBlankDef -> la
      FItem i -> i:la
      FClause EditorBlankClause -> la
      FClause c -> c:la
      FPat EditorBlankPat -> la
      FPat p -> p:la
    insertNameR :: Focus Name -> [String] -> [String]
    insertNameR (FName (Name n)) ln = ln ++ [n]
    insertNameL :: Focus Name -> [String] -> [String]
    insertNameL (FName (Name n)) ln = n:ln 
    markDecChange :: Edit sig m => m ()
    markDecChange = putPart Dec >> markChange >> clearPart
    markItemInsertion :: Edit sig m => m ()
    markItemInsertion = pushName "_" >> markDecChange >> popName

edge :: Direction -> Path a -> Bool
edge d p = case d of
  Left -> case p of
    PTop -> True
    PTermDefName _ _ _ -> True
    PNamespaceDefName _ _ -> True
    PAppTerms _ [] _ -> True
    PIndDefName _ _ _ -> True
    PProdDefName _ _ _ -> True
    PConName _ _ -> True
    PLetName _ _ _ _ -> True
    PPiName _ _ _ -> True
    PMkProdTy _ _ -> True
    PMkIndName _ _ -> True
    PCode _ -> True
    PQuote _ -> True
    PSplice _ -> True
    PMatchScr _ [] _ _ -> True
    PMatchClausePat _ _ -> True
    PPatConName _ _ -> True
    _ -> False
  Right -> case p of
    PTop -> True
    PTermDefBody _ _ _ -> True
    PNamespaceDefItems _ _ _ [] -> True
    PIndDefCons _ _ _ _ [] -> True
    PProdDefFields _ _ _ _ [] -> True
    PConTy _ _ -> True
    PLamBody _ _ -> True
    PAppTerms _ _ [] -> True
    PLetBody _ _ _ _ -> True
    PPiOut _ _ _ -> True
    PMkProdArgs _ _ _ [] -> True
    PMkIndArgs _ _ _ [] -> True
    PCode _ -> True
    PQuote _ -> True
    PSplice _ -> True
    PMatchClauseBody _ _ -> True
    PMatchClause _ _ _ [] -> True
    PPatConArg _ _ _ [] -> True
    _ -> False

atomic :: Focus a -> Bool
atomic focus = case focus of
  FTerm term -> case term of
    Hole -> True
    EditorBlank -> True
    Var _ -> True
    GVar _ -> True
    U0 -> True
    U1 -> True
    _ -> False
  FItem item -> case item of
    EditorBlankDef -> True
    _ -> False
  FCon con -> case con of
    EditorBlankCon -> True
    _ -> False
  FName _ -> True
  FGName _ -> True
  FClause _ -> True
  FPat p -> case p of
    BindingPat _ -> True
    _ -> False

putWord16 :: Word16 -> Put
putWord16 = put

putItem :: Item -> Put
putItem item = case item of
  NamespaceDef (Name n) items -> do
    putWord8 0
    putString n
    putWord16 $ fromIntegral (length items)
    forM_ items putItem
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
    forM_ cons \(Name n, t) -> do
      putString n
      putTerm t
  ProdDef (Name n) ty fields -> do
    putWord8 3
    putString n
    putTerm ty
    putWord16 $ fromIntegral (length fields)
    forM_ fields \field -> putTerm field

putString :: String -> Put
putString s = do
  putWord16 $ fromIntegral (length s)
  forM_ s put

putStrings :: [String] -> Put
putStrings ss = forM_ ss putString

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
    putTerm lam
    putWord16 $ fromIntegral (length args)
    forM_ args putTerm
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
  MkProd ty fields -> do
    putWord8 13
    putTerm ty
    putWord16 $ fromIntegral (length fields)
    forM_ fields putTerm

moveToTop :: Edit sig m => Ex -> m Item
moveToTop (Ex state) =
  run (MoveOut Left) state >>= \case
    ex@(Ex (EditorState (Cursor focus path) _ _)) -> case path of
      PTop -> pure $ unFItem focus
      _ -> moveToTop ex

-- moveToItem :: Edit sig m => Ex -> m Ex
-- moveToItem (Ex state) =
--   run (MoveOut Left) state >>= \case
--     ex@(Ex (EditorState (Cursor focus path) _ _)) -> case itemName path undefined of
--       Just _ -> pure ex
--       _ -> moveToItem ex

export :: EditIO sig m => EditorState a -> String -> m ()
export state@(EditorState cursor _ _) fn = do
  program <- moveToTop (Ex state) 
  let bs = runPut $ putItem program
  handle <- LE.sendIO $ openFile fn WriteMode
  LE.sendIO $ LB.hPut handle bs
  LE.sendIO $ hClose handle

type Render sig m = Has (State [Error]) sig m

render :: EditorState a -> Elab.ElabState -> Item -> (T.Text, [Error])
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
        goFunElim (C.FunElim lam arg _) n args = case traceShowId n of
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
      FocusedName s -> yellow "{" <> T.pack s <> yellow "]"
    renderPi :: Name -> T.Text -> T.Text -> T.Text
    renderPi name inTy outTy = case name of
      FocusedName _ -> "(" <> renderName name <> " : " <> inTy <> ") -> " <> outTy
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

insertFocusMarker :: EditorState a -> EditorState a
insertFocusMarker state@(EditorState (Cursor focus path) ft side) = case ft of
  FTItem -> EditorState (Cursor (FItem $ EditorFocusDef (unFItem focus) side) path) ft side
  FTTerm -> EditorState (Cursor (FTerm $ EditorFocus (unFTerm focus) side) path) ft side
  FTName -> EditorState (Cursor (FName $ FocusedName $ unFNameS focus) path) ft side
  FTGName -> EditorState (Cursor (FGName $ FocusedGName $ unGName $ unFGName focus) path) ft side
  _ -> state

-- Lol just Ctrl+C + Ctrl+V from StackOverflow. `hSetBuffering stdin NoBuffering` doesn't work on Windows.
getHiddenChar = fmap (chr.fromEnum) c_getch
foreign import ccall unsafe "conio.h getch"
  c_getch :: IO CInt

data TermInsertionType
  = TILam
  | TILet
  | TIApp
  | TIPi
  | TICode
  | TIQuote
  | TISplice
  | TIMkProd
  | TIMkInd
  | TIMatch
  deriving Eq

data Input
  = IQuit
  | IExportFile
  | ILoadFile
  | IThenMoveHardRight (Maybe Input)
  | IThenMoveRight (Maybe Input)
  | IThenMoveLeft (Maybe Input)
  | IInsertTermDef
  | IInsertIndDef
  | IInsertProdDef
  | IInsertNamespaceDef
  | IInsertTerm TermInsertionType
  | IInsertU0
  | IInsertU1
  | IAdd
  | ISetName String
  | IDelete
  deriving Eq

getCommand :: String -> IO Input
getCommand acc = do
  putStr "\ESC[2K"
  putStr "\ESC[1000D"
  putStr (reverse acc)
  hFlush stdout
  c <- getHiddenChar
  case c of
    '\b' ->
      if null acc then
        pure IDelete
      else
        getCommand (tail acc)
    _ -> case parseCommand (c:acc) of
      Just cmd -> pure cmd
      Nothing -> getCommand (c:acc)

split :: String -> String -> Char -> [String]
split s acc d = case s of
  [] -> [acc]
  c:cs ->
    if c == d then
      acc : split cs "" d
    else
      split cs (acc ++ [c]) d

parseCommand :: String -> Maybe Input
parseCommand s = case s of
  "q;" -> Just $ IQuit
  "]" -> Just $ IThenMoveRight Nothing
  "[" -> Just $ IThenMoveLeft Nothing
  " mi;" -> Just $ ILoadFile
  " xe;" -> Just $ IExportFile
  "." -> Just $ IThenMoveHardRight $ Just $ IThenMoveRight $ Just $ IInsertTerm TIApp
  " >-" -> Just $ IThenMoveHardRight $ Just $ IThenMoveRight $ Just $ IThenMoveRight $ Just $ IInsertTerm TIPi
  "#i" -> Just $ IThenMoveRight $ Just $ IInsertTerm TIMkInd
  "#" -> Just $ IThenMoveRight $ Just $ IInsertTerm TIMkProd
  " llarof" -> Just $ IThenMoveRight $ Just $ IInsertTerm TIPi
  " lav" -> Just $ IThenMoveRight $ Just $ IInsertTermDef
  " tel" -> Just $ IThenMoveRight $ Just $ IInsertTerm TILet
  "\\" -> Just $ IThenMoveRight $ Just $ IInsertTerm TILam
  " " -> Just IAdd
  " edoc" -> Just $ IThenMoveRight $ Just $ IInsertTerm TICode
  "<" -> Just $ IThenMoveRight $ Just $ IInsertTerm TIQuote
  "~" -> Just $ IThenMoveRight $ Just $ IInsertTerm TISplice
  " dni" -> Just $ IThenMoveRight $ Just IInsertIndDef
  " sn" -> Just $ IThenMoveRight $ Just IInsertNamespaceDef
  " dorp" -> Just $ IThenMoveRight $ Just IInsertProdDef
  " esac" -> Just $ IThenMoveRight $ Just $ IInsertTerm TIMatch
  ' ':s -> Just $ IThenMoveRight $ Just (go s)
  _ -> Nothing
  where
    go s = case s of
      "0u" -> IInsertU0
      "1u" -> IInsertU1
      _ -> ISetName (reverse s)

moveRight :: Edit sig m => EditorState a -> m Ex
moveRight state = (\c -> run c state) $ case (edge Right (unPath $ unCursor state), atomic (unFocus $ unCursor state), unSide state) of
  (False, False, Left) -> MoveInLeft
  (False, True, Left) -> MoveRight
  (True, False, Left) -> MoveInLeft
  (True, True, Left) -> MoveRight
  (False, False, Right) -> MoveRight
  (False, True, Right) -> MoveRight
  (True, False, Right) -> MoveOut Right
  (True, True, Right) -> MoveOut Right

moveLeft :: Edit sig m => EditorState a -> m Ex
moveLeft state = (\c -> run c state) $ case (edge Left (unPath $ unCursor state), atomic (unFocus $ unCursor state), unSide state) of
  (False, False, Left) -> MoveLeft
  (False, True, Left) -> MoveLeft
  (True, False, Left) -> MoveOut Left
  (True, True, Left) -> MoveOut Left
  (False, False, Right) -> MoveInRight
  (False, True, Right) -> MoveLeft
  (True, False, Right) -> MoveInRight
  (True, True, Right) -> MoveLeft

handleInput :: EditIO sig m => EditorState a -> Input -> m Ex
handleInput state input = case (input, unFocusType state) of
  (IExportFile, _) -> do
    fn <- LE.sendIO $ getLine
    export state fn
    pure $ Ex state
  (ILoadFile, _) -> do
    fn <- LE.sendIO $ getLine
    handle <- LE.sendIO $ openFile fn ReadMode
    bs' <- LE.sendIO $ LB.hGetContents handle
    let !bs = bs'
    let program = runGet getItem bs
    LE.sendIO $ hClose handle
    pure $ mkEx program PTop Left
  (IThenMoveHardRight input', _) -> do
    (Ex state') <- case input' of
      Just input' -> handleInput state input'
      Nothing -> pure $ Ex state
    run MoveRight state'
  (IThenMoveRight input', _) -> do
    (Ex state') <- case input' of
      Just input' -> handleInput state input'
      Nothing -> pure $ Ex state
    moveRight state'
  (IThenMoveLeft input', _) -> do
    (Ex state') <- case input' of
      Just input' -> handleInput state input'
      Nothing -> pure $ Ex state
    moveLeft state'
  -- ("al", _) -> run (Add Left) state
  (IAdd, _) -> run Add state
  -- ("d", FTTerm) -> run InsertHole state
  (IInsertTerm ti, FTTerm) -> run (InsertTerm ti) state
  (IInsertU0, FTTerm) -> run InsertU0 state
  (IInsertU1, FTTerm) -> run InsertU1 state
  (IInsertNamespaceDef, FTItem) -> run InsertNamespaceDef state
  (IInsertTermDef, FTItem) -> run InsertTermDef state
  (IInsertIndDef, FTItem) -> run InsertIndDef state
  (IInsertProdDef, FTItem) -> run InsertProdDef state
  (ISetName s, FTTerm) -> case split s "" '.' of
    [n] -> run (InsertVar n) state
    ns -> run (InsertGVar $ reverse ns) state
  (ISetName s, FTGName) -> run (SetGName $ reverse $ split s "" '.') state
  (ISetName s, FTName) -> if s == "" then pure $ Ex state else run (SetName s) state
  (ISetName s, FTCon) -> if s == "" then pure $ Ex state else run (InsertCon s) state
  (IDelete, _) -> run Delete state
  _ -> pure $ Ex state

renderError :: Error -> T.Text
renderError (Error _ _ _ err) = case err of
  UnboundLocal (Name name) -> yellow "Unbound local variable " <> "`" <> T.pack name <> "`"
  UnboundGlobal (GName gname) -> yellow "Unbound global variable " <> "`" <> T.intercalate "." (map T.pack gname)
  UnifyError err -> yellow "Failed to unify:\n" <> T.pack (show err)
  TooManyParams -> yellow "Too many parameters"
  MalformedProdDec -> yellow "Malformed product declaration"
  ExpectedProdType -> yellow "Expected a product type"
  MismatchedFieldNumber -> yellow "Mismatched field number"

loop :: EditIO sig m => EditorState a -> m ()
loop state = do
  LE.sendIO $ clearScreen
  -- (GName ns) <- SE.get
  -- part <- SE.get @(Maybe ItemPart)
  -- changes <- SE.get @Changes
  -- LE.sendIO $ putStrLn $ show changes
  SE.put @Changes mempty
  -- LE.sendIO $ putStrLn $ show part
  -- LE.sendIO $ putStrLn $ show ns
  item <- moveToTop $ Ex $ insertFocusMarker state
  -- LE.sendIO $ putStrLn $ show item
  -- LE.sendIO $ putStrLn $ show item'
  let (cTerm, elabState) = Elab.elabFresh item
  -- LE.sendIO $ putStrLn $ show cTerm
  let (s, es) = render state elabState item
  LE.sendIO $ TIO.putStrLn (s <> "\n")
  forM_ es (LE.sendIO . TIO.putStrLn . renderError)
  -- LE.sendIO $ putStrLn $ show es
  LE.sendIO $ hFlush stdout
  input <- LE.sendIO $ getCommand ""
  if input == IQuit then
    pure ()
  else do
    state <- handleInput state input
    next state
    where
      next :: EditIO sig m => Ex -> m ()
      next (Ex state) = loop state

main :: IO ()
main = do
  setLocaleEncoding utf8
  putStr "\ESC[0m"
  state <-
    runM @IO .
    runState @GName (GName ["main"]) .
    runState @Changes DM.empty .
    runState @(Maybe ItemPart) Nothing $
    loop (EditorState (Cursor (FName $ Name "main") (PNamespaceDefName PTop [])) FTName Left)
  pure ()