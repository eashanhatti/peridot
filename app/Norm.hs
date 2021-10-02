{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
-- {-# OPTIONS_GHC -fdefer-type-errors #-}

module Norm where

import Var
import qualified Core as C
import qualified Data.Map as Map
import Data.Maybe(fromJust)
import Debug.Trace
import Control.Monad.Reader
import qualified Data.Set as Set
import GHC.Stack
import Data.List(intersperse)
import Numeric.Natural

data MetaEntry a = Solved a | Unsolved
  deriving Show

type Metas = Map.Map Global (MetaEntry Value)
type Locals = [Value]

type Spine = [Value]
data Closure = Closure [Value] C.Term
  deriving Show

-- Type annotation
type Type = Value

data Value
  = FunIntro Closure Type
  | FunType Type Closure
  | QuoteIntro C.Term Type
  | QuoteType Value
  | FinIntro Natural Type
  | FinType Natural
  | PairIntro Value Value Type
  | PairType Value Value
  | TypeType0
  | TypeType1
  -- Blocked eliminations
  | StuckFlexVar Type Global Spine
  | StuckRigidVar Type Level Spine
  | StuckSplice Value
  | StuckFinCase Value [Value]
  | StuckSplit Value C.Term
  -- Object-level terms, should only appear under quotes
  | FunElim0 Value Value
  | Var0 Index Value
  | Letrec0 [Value] Value
  -- | Let0 Value Value Value
  -- Extras
  | LetrecBound Closure
  | ElabError
  | ElabBlank

instance Show Value where
  show v = case v of
    FunIntro (Closure _ body) ty -> "v{" ++ show body ++ "}"
    FunType inTy (Closure env outTy) -> show inTy ++ " v-> " ++ show outTy ++ " " ++ show env
    QuoteIntro inner _ -> "v<" ++ show inner ++ ">"
    QuoteType innerTy -> "vQuote " ++ show innerTy
    FinIntro n _ -> "vfin" ++ show n
    FinType n -> "vFin" ++ show n
    PairIntro proj0 proj1 _ -> "vpair " ++ show proj0 ++ " * " ++ show proj1
    PairType pty0 pty1 -> "vPair " ++ show pty0 ++ " * " ++ show pty1
    TypeType0 -> "vU0"
    TypeType1 -> "vU1"
    StuckFlexVar _ gl spine -> "v~(?" ++ show (unGlobal gl) ++ " " ++ (concat $ intersperse " " (map show spine)) ++ ")"
    StuckRigidVar ty lv spine -> "v~(" ++ show (unLevel lv) ++ " " ++ (concat $ intersperse " " (map show spine)) ++ "; : " ++ show ty ++ ")"
    FunElim0 lam arg -> "v(" ++ show lam ++ " @ " ++ show arg ++ ")"
    StuckSplice quote -> "v[" ++ show quote ++ "]"
    StuckFinCase scr bs -> "vcase " ++ show scr ++ show (map show bs)
    StuckSplit scr body -> "vsplit " ++ show scr ++ " in " ++ show body
    LetrecBound v -> "lrb(" ++ show v ++ ")"
    ElabError -> "v<error>"
    ElabBlank -> "v<blank>"
    _ -> error $ show v

type Norm a = Reader (Level, Metas, Locals) a

askLv :: Norm Level
askLv = do
  (lv, _, _) <- ask
  pure lv

askMetas :: Norm Metas
askMetas = do
  (_, metas, _) <- ask
  pure metas

askLocals :: Norm Locals
askLocals = do
  (_, _, locals) <- ask
  pure locals

appClosure :: HasCallStack => Closure -> Value -> Norm Value
appClosure (Closure locals body) val = do
  (level, metas, _) <- ask
  pure $ runReader (eval body) (level, metas, val:locals)

vApp :: HasCallStack => Value -> Value -> Norm Value
vApp lam arg = case lam of
  FunIntro body vty -> appClosure body arg
  StuckFlexVar vty gl spine -> pure $ StuckFlexVar vty gl (arg:spine)
  StuckRigidVar vty lv spine -> pure $ StuckRigidVar vty lv (arg:spine)
  _ -> error $ "Cannot `vApp` `" ++ show lam ++ "`"

vSplice :: HasCallStack => Value -> Norm Value
vSplice val = case val of
  QuoteIntro inner _ -> eval0 inner
  _ -> pure $ StuckSplice val

vFinCase :: HasCallStack => Value -> [Value] -> Norm Value
vFinCase scr bs = case scr of
  FinIntro n _ -> pure $ bs !! fromIntegral n
  _ -> pure $ StuckFinCase scr bs

vSplit :: HasCallStack => Value -> C.Term -> Norm Value
vSplit scr body = case scr of
  PairIntro proj0 proj1 _ -> define proj1 $ define proj0 $ eval body
  _ -> pure $ StuckSplit scr body

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

vMeta :: HasCallStack => Global -> Type -> Norm Value
vMeta gl vty = do
  metas <- askMetas
  pure $ case fromJust $ Map.lookup gl metas of
    Solved sol -> sol
    Unsolved -> StuckFlexVar vty gl []

bind :: HasCallStack => Value -> Norm a -> Norm a
bind ty act = do
  (level, metas, locals) <- ask
  pure $ runReader act (incLevel level, metas, (StuckRigidVar ty level []):locals)

define :: HasCallStack => Value -> Norm a -> Norm a
define val act = do
  (level, metas, locals) <- ask
  pure $ runReader act (incLevel level, metas, val:locals)

blank :: HasCallStack => Norm a -> Norm a
blank act = do
  (level, metas, locals) <- ask
  pure $ runReader act (incLevel level, metas, ElabBlank:locals)

blankN :: HasCallStack => Int -> Norm a -> Norm a
blankN n act = case n of
  0 -> act
  n -> blank $ blankN (n - 1) act

index :: HasCallStack => Metas -> Locals -> Index -> C.Type -> Int -> Value
index metas locals ix ty ix' = case locals of
  [] -> {-ElabError-} error $ "Nonexistent var `" ++ show ix ++ " : " ++ show ty ++ "`"
  x:xs ->
    if ix' == 0 then
      case x of
        LetrecBound (Closure locals' def) -> runReader (eval def) (Level 0, metas, locals')
        _ -> x
    else
      index metas xs ix ty (ix' - 1)

eval0 :: HasCallStack => C.Term -> Norm Value
eval0 term = do
  (_, _, locals) <- ask
  case term of
    C.Var ix ty -> Var0 ix <$> eval0 ty
    C.TypeType0 -> pure TypeType0
    C.FunIntro body ty -> FunIntro (Closure locals body) <$> eval0 ty
    C.FunType inTy outTy -> do
      vInTy <- eval0 inTy
      pure $ FunType vInTy (Closure locals outTy)
    C.FunElim lam arg -> FunElim0 <$> eval0 lam <*> eval0 arg
    C.QuoteElim quote -> eval quote >>= vSplice
    -- C.Let def defTy body -> do
    --   vDef <- eval0 def
    --   vDefTy <- eval0 defTy
    --   vBody <- blank $ eval0 body
    --   pure $ Let0 vDef vDefTy vBody
    C.Letrec defs body -> do
      vDefs <- mapM (\def -> blankN (length defs) $ eval0 def) defs
      vBody <- blankN (length defs) $ eval0 body
      pure $ Letrec0 vDefs vBody
    _ -> error $ "`eval0` unreachable: " ++ show term

eval :: HasCallStack => C.Term -> Norm Value
eval term = do
  (_, metas, locals) <- ask
  case term of
    C.Var ix ty -> pure $ index metas locals ix ty (unIndex ix)
    C.TypeType0 -> pure TypeType0
    C.TypeType1 -> pure TypeType1
    C.FunIntro body ty -> FunIntro (Closure locals body) <$> eval ty
    C.FunType inTy outTy -> do
      vInTy <- eval inTy
      pure $ FunType vInTy (Closure locals outTy)
    C.FunElim lam arg -> do
      vLam <- eval lam
      vArg <- eval arg
      vApp vLam vArg
    C.QuoteIntro inner ty -> QuoteIntro <$> pure inner <*> eval ty
    C.QuoteType innerTy -> QuoteType <$> eval innerTy
    C.QuoteElim quote -> eval quote >>= vSplice
    C.FinIntro n ty -> FinIntro n <$> eval ty
    C.FinType n -> pure $ FinType n
    C.FinElim scr bs -> do
      vScr <- eval scr
      vBs <- mapM eval bs
      vFinCase vScr vBs
    C.PairIntro proj0 proj1 ty -> do
      vProj0 <- eval proj0
      vProj1 <- define vProj0 $ eval proj1
      vTy <- eval ty
      pure $ PairIntro vProj0 vProj1 vTy
    C.PairType pty0 pty1 -> do
      vPty0 <- eval pty0
      vPty1 <- bind vPty0 $ eval pty1
      pure $ PairType vPty0 vPty1
    C.PairElim scr body -> eval scr >>= \vScr -> vSplit vScr body 
    -- C.Let def _ body -> do
    --   vDef <- eval def
    --   define vDef $ eval body
    C.Letrec defs body -> do
      let withDefs :: Norm a -> Locals -> Norm a
          withDefs act defs = do
            (level, metas, locals) <- ask
            pure $ runReader act (level, metas, defs ++ locals)
      let vDefs = map (\def -> LetrecBound $ Closure (reverse vDefs ++ locals) def) defs
      -- let !() = trace ("Enter") ()
      -- let !() = traceShow vDefs ()
      eval body `withDefs` (reverse vDefs)
    C.Meta gl ty -> eval ty >>= vMeta gl
    C.InsertedMeta bis gl ty -> eval ty >>= vMeta gl >>= \meta -> vAppBis meta locals bis
    C.ElabError -> pure ElabError

force :: HasCallStack => Value -> Norm Value
force val = do
  metas <- askMetas
  case val of
    StuckFlexVar vty gl spine | Solved sol <- fromJust $ Map.lookup gl metas -> do
      sol <- vAppSpine sol spine
      force sol
    _ -> pure val

lvToIx :: Level -> Level -> Index
lvToIx lv1 lv2 = Index (unLevel lv1 - unLevel lv2 - 1)

readbackSpine :: HasCallStack => C.Term -> Spine -> Norm C.Term
readbackSpine term spine = do
  case spine of
    arg:spine -> C.FunElim <$> readbackSpine term spine <*> readback arg
    [] -> pure term

readback0 :: HasCallStack => Value -> Norm C.Term
readback0 val = case val of
  TypeType0 -> pure C.TypeType0
  FunElim0 lam arg -> C.FunElim <$> readback0 lam <*> readback0 arg
  Letrec0 defs body -> do
    cDefs <- mapM (\def -> blankN (length defs) $ readback0 def) defs
    cBody <- blankN (length defs) $ readback0 body
    pure $ C.Letrec cDefs cBody
  Var0 ix ty -> C.Var ix <$> readback0 ty
  StuckSplice quote -> C.QuoteElim <$> readback quote

-- TODO? replace `bind` with `blank`
readback :: HasCallStack => Value -> Norm C.Term
readback val = do
  val <- force val
  case val of
    StuckFlexVar vty gl spine -> do
      meta <- C.Meta <$> pure gl <*> readback vty
      readbackSpine meta spine
    StuckRigidVar vty lv' spine -> do
      lv <- askLv
      var <- C.Var <$> pure (lvToIx lv lv') <*> readback vty
      readbackSpine var spine
    StuckSplice quote -> C.QuoteElim <$> readback quote
    StuckFinCase scr bs -> C.FinElim <$> readback scr <*> mapM readback bs
    StuckSplit scr body -> C.PairElim <$> readback scr <*> pure body
    FunIntro body vty@(FunType inTy _) -> do
      lv <- askLv
      vBody <- appClosure body (StuckRigidVar inTy lv [])
      C.FunIntro <$> blank (readback vBody) <*> readback vty
    FunType inTy outTy@(Closure env tmp) -> do
      lv <- askLv
      vOutTy <- appClosure outTy (StuckRigidVar inTy lv [])
      C.FunType <$> readback inTy <*> blank (readback vOutTy)
    QuoteIntro inner ty -> C.QuoteIntro <$> (eval0 inner >>= readback) <*> readback ty
    QuoteType innerTy -> C.QuoteType <$> readback innerTy
    PairIntro proj0 proj1 ty -> C.PairIntro <$> readback proj0 <*> blank (readback proj1) <*> readback ty
    PairType pty0 pty1 -> C.PairType <$> readback pty0 <*> blank (readback pty1)
    FinIntro n ty -> C.FinIntro n <$> readback ty
    FinType n -> pure $ C.FinType n
    TypeType0 -> pure C.TypeType0
    TypeType1 -> pure C.TypeType1
    ElabError -> pure C.ElabError