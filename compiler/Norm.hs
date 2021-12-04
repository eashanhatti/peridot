{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}
-- {-# OPTIONS_GHC -fdefer-type-errors #-}

module Norm where

import Var
import qualified Core as C
import qualified Surface as S
import qualified Data.Map as Map
import Data.Maybe(fromJust)
import Debug.Trace
import Control.Monad.Reader
import qualified Data.Set as Set
import GHC.Stack
import Data.List(intersperse)
import Numeric.Natural
import Etc
import {-# SOURCE #-} Elaboration.Error

data MetaEntry a = Solved a | Unsolved
  deriving Show

type Metas = Map.Map Global (MetaEntry Value)
type Globals = Map.Map Id C.Item
type Locals = [Value]

type Spine = [Value]
data Closure = Closure [Value] C.Term
  deriving (Show, Eq)

-- Type annotation
type Type = Value

data Value = Value
  { unInfo :: C.Info
  , unVal :: ValueInner }
  deriving Eq

data ValueInner
  = FunIntro Closure Type C.FunIntroInfo
  | FunType Type Closure C.FunTypeInfo
  | QuoteIntro C.Term Type
  | QuoteType Value
  | IndType Id [Value]
  | IndIntro Id [Value] Type
  | ProdType Id [Value]
  | ProdIntro Type [Value]
  | TypeType0
  | TypeType1
  -- Blocked eliminations
  | StuckFlexVar (Maybe Type) Global Spine
  | StuckGVar Id Type C.GVarInfo
  | StuckRigidVar Type Level Spine C.VarInfo
  | StuckSplice Value
  -- Object-level terms, should only appear under quotes
  | FunElim0 Value Value C.FunElimInfo
  | Var0 Index Value C.VarInfo
  | Letrec0 [Value] Value C.LetrecInfo
  -- | Let0 Value Value Value
  -- Extras
  | LetrecBound Closure
  | ElabError S.Term
  | ElabBlank
  deriving Eq

gen v = Value (C.Info Nothing []) v

instance Show Value where
  show (Value _ v) = case v of
    FunIntro (Closure _ body) ty _ -> "v{" ++ show body ++ "}"
    FunType inTy (Closure env outTy) _ -> show inTy ++ " v-> " ++ show outTy ++ " " ++ show env
    QuoteIntro inner _ -> "v<" ++ show inner ++ ">"
    QuoteType innerTy -> "vQuote " ++ show innerTy
    TypeType0 -> "vU0"
    TypeType1 -> "vU1"
    StuckFlexVar _ gl spine -> "v~(?" ++ show (unGlobal gl) ++ " " ++ (concat $ intersperse " " (map show spine)) ++ ")"
    StuckRigidVar ty lv spine _ -> "v~(" ++ show (unLevel lv) ++ " " ++ (concat $ intersperse " " (map show spine)) ++ "; : " {-++ show ty-} ++ ")"
    FunElim0 lam arg _ -> "v(" ++ show lam ++ " @ " ++ show arg ++ ")"
    StuckSplice quote -> "v[" ++ show quote ++ "]"
    LetrecBound v -> "lrb(" ++ show v ++ ")"
    ElabError s -> "error(" ++ show s ++ ")"
    ElabBlank -> "v<blank>"
    StuckGVar nid ty _ -> "(vg" ++ show nid ++ " : " ++ show ty ++ ")"
    IndType nid indices -> "vT" ++ show nid ++ "[" ++ (concat $ intersperse " " (map show indices)) ++ "]"
    IndIntro nid args _ -> "(v$" ++ show nid ++ (concat $ intersperse " " (map show args)) ++ ")"
    ProdType nid indices -> "vP" ++ show nid ++ "[" ++ (concat $ intersperse " " (map show indices)) ++ "]"
    ProdIntro ty args -> "{" ++ (concat $ intersperse " " (map show args)) ++ "} : " ++ show ty

type Norm a = Reader (Level, Metas, Locals, Globals) a

askLv :: Norm Level
askLv = do
  (lv, _, _, _) <- ask
  pure lv

askMetas :: Norm Metas
askMetas = do
  (_, metas, _, _) <- ask
  pure metas

askLocals :: Norm Locals
askLocals = do
  (_, _, locals, _) <- ask
  pure locals

appClosure :: HasCallStack => Closure -> Value -> Norm Value
appClosure (Closure locals body) val = do
  (level, metas, _, globals) <- ask
  pure $ runReader (eval body) (level, metas, val:locals, globals)

vApp :: HasCallStack => Value -> Value -> Norm Value
vApp (Value info lam) arg = case lam of
  FunIntro body vty _ -> appClosure body arg
  StuckFlexVar vty gl spine -> Value info <$> (pure $ StuckFlexVar vty gl (arg:spine))
  StuckRigidVar vty lv spine _ -> Value info <$> (pure $ StuckRigidVar vty lv (arg:spine) (C.VarInfo "_")) -- FIXME
  _ -> pure $ gen ElabBlank

vSplice :: HasCallStack => Value -> Norm Value
vSplice val = case unVal val of
  QuoteIntro inner _ -> eval0 inner
  _ -> pure $ gen $ StuckSplice val

vAppSpine :: HasCallStack => Value -> Spine -> Norm Value
vAppSpine val spine = case spine of
  arg:spine -> do
    lam <- vAppSpine val spine
    vApp lam arg
  [] -> pure val

vAppBis :: HasCallStack => Value -> Locals -> [C.BinderInfo] -> Norm Value
vAppBis val locals bis = do
  case (locals, bis) of
    (local:locals, C.Abstract:bis) -> do
      lam <- vAppBis val locals bis
      vApp lam local
    (_:locals, C.Concrete:bis) -> vAppBis val locals bis
    ([], []) -> pure val
    _ -> error ("impossible\n" ++ show locals ++ "\n" ++ show bis ++ "\n" ++ show val)

vMeta :: HasCallStack => Global -> Maybe Type -> Norm Value
vMeta gl vty = do
  metas <- askMetas
  pure $ case fromJust $ Map.lookup gl metas of
    Solved sol -> sol
    Unsolved -> gen $ StuckFlexVar vty gl []

bind :: HasCallStack => Value -> Norm a -> Norm a
bind ty act = do
  (level, metas, locals, globals) <- ask
  pure $ runReader act (incLevel level, metas, (gen $ StuckRigidVar ty level [] (C.VarInfo "_")):locals, globals) -- FIXME

define :: HasCallStack => Value -> Norm a -> Norm a
define val act = do
  (level, metas, locals, globals) <- ask
  pure $ runReader act (incLevel level, metas, val:locals, globals)

blank :: HasCallStack => Norm a -> Norm a
blank act = do
  (level, metas, locals, globals) <- ask
  pure $ runReader act (incLevel level, metas, (gen ElabBlank):locals, globals)

blankN :: HasCallStack => Int -> Norm a -> Norm a
blankN n act = case n of
  0 -> act
  n -> blank $ blankN (n - 1) act

index :: HasCallStack => Metas -> Locals -> Globals -> Index -> C.Type -> Int -> Value
index metas locals globals ix ty ix' = case locals of
  [] -> gen ElabBlank
  x:xs ->
    if ix' == 0 then
      case unVal x of
        LetrecBound (Closure locals' def) -> runReader (eval def) (Level 0, metas, locals', globals)
        _ -> x
    else
      index metas xs globals ix ty (ix' - 1)

eval0 :: HasCallStack => C.Term -> Norm Value
eval0 (C.Term info term) = do
  (_, _, locals, _) <- ask
  Value info <$> case term of
    C.Var ix ty info -> Var0 ix <$> eval0 ty <*> pure info
    C.TypeType0 -> pure TypeType0
    C.FunIntro body ty info -> FunIntro (Closure locals body) <$> eval0 ty <*> pure info
    C.FunType inTy outTy info -> do
      vInTy <- eval0 inTy
      pure $ FunType vInTy (Closure locals outTy) info
    C.FunElim lam arg info -> FunElim0 <$> eval0 lam <*> eval0 arg <*> pure info
    C.QuoteElim quote -> unVal <$> (eval quote >>= vSplice)
    C.ProdIntro ty fields -> ProdIntro <$> eval0 ty <*> mapM eval0 fields
    C.Letrec defs body info' -> do
      vDefs <- mapM (\def -> blankN (length defs) $ eval0 def) defs
      vBody <- blankN (length defs) $ eval0 body
      pure $ Letrec0 vDefs vBody info'
    C.ElabError s -> pure $ ElabError s

eval :: HasCallStack => C.Term -> Norm Value
eval (C.Term info term) = do
  (_, metas, locals, globals) <- ask
  case term of
    C.Var ix ty _ -> pure $ index metas locals globals ix ty (unIndex ix)
    C.TypeType0 -> pure $ Value info TypeType0
    C.TypeType1 -> pure $ Value info TypeType1
    C.FunIntro body ty info' -> Value info <$> (FunIntro (Closure locals body) <$> eval ty <*> pure info')
    C.FunType inTy outTy info' -> do
      vInTy <- eval inTy
      pure $ Value info $ (FunType vInTy (Closure locals outTy) info')
    C.FunElim lam arg _ -> do
      vLam <- eval lam
      vArg <- eval arg
      vApp vLam vArg
    C.QuoteIntro inner ty -> Value info <$> (QuoteIntro <$> pure inner <*> eval ty)
    C.QuoteType innerTy -> Value info <$> (QuoteType <$> eval innerTy)
    C.QuoteElim quote -> eval quote >>= vSplice
    C.IndIntro cid cds ty -> Value info <$> (IndIntro cid <$> mapM eval cds <*> eval ty)
    C.IndType nid indices -> mapM eval indices >>= \is -> pure $ Value info $ IndType nid is
    C.ProdType nid indices -> mapM eval indices >>= \is -> pure $ Value info $ ProdType nid is
    C.ProdIntro ty fields -> do
      vTy <- eval ty
      vFields <- mapM eval fields
      pure $ Value info $ ProdIntro vTy vFields
    C.Letrec defs body _ -> do
      let withDefs :: Norm a -> Locals -> Norm a
          withDefs act defs = do
            (level, metas, locals, globals) <- ask
            pure $ runReader act (level, metas, defs ++ locals, globals)
      let vDefs = map (\def -> gen $ LetrecBound $ Closure (reverse vDefs ++ locals) def) defs
      -- let !() = trace ("Enter") ()
      -- let !() = traceShow vDefs ()
      eval body `withDefs` (reverse vDefs)
    C.Meta gl ty -> case fmap eval ty of
      Just ty -> ty >>= \ty -> vMeta gl (Just ty)
      Nothing -> vMeta gl Nothing
    C.InsertedMeta bis gl ty -> case ty of
      Just ty -> eval ty >>= \ty -> vMeta gl (Just ty) >>= \meta -> vAppBis meta locals bis
      Nothing -> vMeta gl Nothing >>= \meta -> vAppBis meta locals bis
    C.GVar nid ty info' -> case fromJust $ Map.lookup nid globals of
      C.TermDef _ def _ -> eval def
      C.IndDef nid ty _ -> do
        nTy <- eval ty >>= readback
        eval $ go nTy []
        where
          go :: C.Term -> [C.Term] -> C.Term
          go ty acc = case C.unTerm $ ty of
            C.FunType inTy outTy (C.FunTypeInfo s) -> C.gen $ C.FunIntro (go outTy (C.gen (C.Var (Index $ length acc) inTy (C.VarInfo $ S.unName s)) : acc)) ty (C.FunIntroInfo 1 s) -- FIXME
            C.TypeType1 -> C.gen $ C.IndType nid acc
      C.ConDef nid ty -> do
        nTy <- eval ty >>= readback
        eval $ go nTy []
        where
          go :: C.Term -> [C.Term] -> C.Term
          go ty acc = case C.unTerm $ ty of
            C.FunType inTy outTy (C.FunTypeInfo s) -> C.gen $ C.FunIntro (go outTy (C.gen (C.Var (Index $ length acc) inTy (C.VarInfo $ S.unName s)) : acc)) ty (C.FunIntroInfo 1 s) -- FIXME
            C.IndType tid indices -> C.gen $ C.IndIntro nid acc (C.gen $ C.IndType tid indices)
      C.ProdDef nid ty fields -> do
        nTy <- eval ty >>= readback
        eval $ go nTy []
        where
          go :: C.Term -> [C.Term] -> C.Term
          go ty acc = case C.unTerm ty of
            C.FunType inTy outTy (C.FunTypeInfo s) -> C.gen $ C.FunIntro (go outTy (C.gen (C.Var (Index $ length acc) inTy (C.VarInfo $ S.unName s)) : acc)) ty (C.FunIntroInfo 1 s) -- FIXME
            C.TypeType0 -> C.gen $ C.ProdType nid acc
      C.ElabBlankItem nid ty -> eval ty >>= \ty -> pure $ Value info $ StuckGVar nid ty info'
    C.ElabError s -> Value info <$> pure (ElabError s)

force :: HasCallStack => Value -> Norm Value
force val@(Value info val') = do
  metas <- askMetas
  case val' of
    StuckFlexVar vty gl spine | Solved sol <- fromJust $ Map.lookup gl metas -> do
      sol <- vAppSpine sol spine
      force sol
    _ -> pure val

lvToIx :: Level -> Level -> Index
lvToIx lv1 lv2 = Index (unLevel lv1 - unLevel lv2 - 1)

readbackSpine :: HasCallStack => C.Term -> Spine -> Norm C.Term
readbackSpine term@(C.Term info term') spine = C.Term info <$> do
  case spine of
    arg:spine -> C.FunElim <$> readbackSpine term spine <*> readback arg <*> pure (C.FunElimInfo 1) -- FIXME
    [] -> pure term'

readback0 :: HasCallStack => Value -> Norm C.Term
readback0 (Value info val) = C.Term info <$> case val of
  TypeType0 -> pure C.TypeType0
  FunElim0 lam arg info -> C.FunElim <$> readback0 lam <*> readback0 arg <*> pure info
  Letrec0 defs body info' -> do
    cDefs <- mapM (\def -> blankN (length defs) $ readback0 def) defs
    cBody <- blankN (length defs) $ readback0 body
    pure $ C.Letrec cDefs cBody info'
  ProdIntro ty fields -> do
    cTy <- readback0 ty
    cFields <- mapM readback0 fields
    pure $ C.ProdIntro cTy cFields
  Var0 ix ty info -> C.Var ix <$> readback0 ty <*> pure info
  StuckSplice quote -> C.QuoteElim <$> readback quote

-- TODO? replace `bind` with `blank`
readback :: HasCallStack => Value -> Norm C.Term
readback val = do
  (Value info val) <- force val
  C.Term info <$> case val of
    StuckFlexVar vty gl spine -> do
      let
        cty = case vty of
          Just vty -> Just <$> readback vty
          Nothing -> pure Nothing
      meta <- C.Meta <$> pure gl <*> cty
      C.unTerm <$> readbackSpine (C.Term info meta) spine
    StuckRigidVar vty lv' spine info' -> do
      lv <- askLv
      var <- C.Var <$> pure (lvToIx lv lv') <*> readback vty <*> pure info'
      C.unTerm <$> readbackSpine (C.Term info var) spine
    StuckSplice quote -> C.QuoteElim <$> readback quote
    FunIntro body vty@(unVal -> FunType inTy _ _) info@(C.FunIntroInfo _ s) -> do
      lv <- askLv
      vBody <- appClosure body (gen $ StuckRigidVar inTy lv [] (C.VarInfo $ S.unName s))
      C.FunIntro <$> blank (readback vBody) <*> readback vty <*> pure info
    FunType inTy outTy@(Closure env tmp) info@(C.FunTypeInfo s) -> do
      lv <- askLv
      vOutTy <- appClosure outTy (gen $ StuckRigidVar inTy lv [] (C.VarInfo $ S.unName s))
      C.FunType <$> readback inTy <*> blank (readback vOutTy) <*> pure info
    IndIntro nid cds ty -> C.IndIntro nid <$> mapM readback cds <*> readback ty
    IndType nid indices -> mapM readback indices >>= pure . C.IndType nid
    QuoteIntro inner ty -> C.QuoteIntro <$> (eval0 inner >>= readback) <*> readback ty
    QuoteType innerTy -> C.QuoteType <$> readback innerTy
    ProdType nid indices -> mapM readback indices >>= pure . C.ProdType nid 
    ProdIntro ty fields -> do
      cTy <- readback ty
      cFields <- mapM readback fields
      pure $ C.ProdIntro cTy cFields
    TypeType0 -> pure C.TypeType0
    TypeType1 -> pure C.TypeType1
    StuckGVar nid ty info -> readback ty >>= \ty -> pure $ C.GVar nid ty info 
    ElabError s -> pure $ C.ElabError s