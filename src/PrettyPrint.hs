module PrettyPrint where

import Control.Algebra
import Control.Effect.Reader(Reader, ask, local)
import Control.Carrier.Reader
import Control.Effect.State(State, get, put, modify)
import Control.Carrier.State.Strict
import Syntax.Core
import Data.Text hiding(zip, foldl', null)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Syntax.Common(Id(..), Index(..))
import Data.Char
import Control.Monad
import Prelude hiding(zip, foldl', intercalate, words, lines, unlines)
import Data.Foldable
import Data.Sequence hiding(singleton, foldl', replicateM, null)
import Extra
import Prelude qualified as P
import Numeric.Natural

data PrintContext = PrintContext
  { unLocals :: Map.Map Index Text
  , unUVEqs :: Map.Map Natural Natural }

data PrintState = PrintState
  { unNextName :: Int
  , unUVNames :: Map.Map Natural Text }

type Print sig m =
  ( Has (Reader PrintContext) sig m
  , Has (State PrintState) sig m )

indentS = P.unlines . fmap ("  "<>) . P.lines
indent = unlines . fmap ("  "<>) . lines

prettyPPm :: PassMethod -> Text
prettyPPm Unification = "inf "
prettyPPm Explicit = ""

pretty :: Print sig m => Term -> m Text
pretty term =
  case term of
    (viewObjFunTys -> (inTys@(_:<|_), outTy)) -> do
      names <- traverse (const freshName) inTys
      params <-
        traverse
          (\(name, (pm, inTy)) -> ((prettyPPm pm <> name <> ": ") <>) <$> pretty inTy)
          (zip names inTys)
      tOutTy <- bindManyLocals names (pretty outTy)
      pure ("Fun(" <> intercalate ", " (toList params) <> ") -> " <> tOutTy)
    (viewMetaFunTys -> (inTys@(_:<|_), outTy)) -> do
      names <- traverse (const freshName) inTys
      params <-
        traverse
          (\(name, (pm, inTy)) -> ((prettyPPm pm <> name <> ": ") <>) <$> pretty inTy)
          (zip names inTys)
      tOutTy <- bindManyLocals names (pretty outTy)
      pure ("MetaFun(" <> intercalate ", " (toList params) <> ") -> " <> tOutTy)
    (viewObjFunIntros -> (n@((> 0) -> True), body)) -> do
      names <- replicateM (fromIntegral n) freshName
      (("fun(" <> intercalate ", " names <> ") => ") <>) <$>
        bindManyLocals (fromList names) (pretty body)
    (viewMetaFunIntros -> (n@((> 0) -> True), body)) -> do
      names <- replicateM (fromIntegral n) freshName
      (("metafun(" <> intercalate ", " names <> ") => ") <>) <$>
        bindManyLocals (fromList names) (pretty body)
    TwoElim scr body1 body2 ->
      combine
        [ pure "if "
        , pretty scr
        , pure " { "
        , pretty body1
        , pure " } else { "
        , pretty body2 ]
    RecType tys -> do
      tTys <- traverse (\(fd, ty) -> ((unField fd <> ": ") <>) <$> pretty ty) tys
      if null tTys then
        pure ("Struct { }")
      else
        pure ("Struct { " <> intercalate ", " (toList tTys) <> " }")
    RecIntro defs -> do
      tDefs <- traverse (\(fd, def) -> ((unField fd <> " = ") <>) <$> pretty def) defs
      if null tDefs then
        pure ("struct { }")
      else
        pure ("struct { " <> intercalate ", " (toList tDefs) <> " }")
    RecElim str fd -> combine [pretty str, pure ("." <> unField fd)]
    SingElim sing -> pretty sing
    (viewFunElims -> (lam, args@(_:<|_))) -> do
      tLam <- pretty lam
      let
        tLam' =
          case words tLam of
            _:[] -> tLam
            _:_ -> "(" <> tLam <> ")"
      combine
        [ pure tLam'
        , pure "("
        , intercalate ", " . toList <$> traverse pretty args, pure ")"]
    CodeObjElim quote -> combine [pure "~", pretty quote]
    CodeCElim quote -> combine [pure "c~", pretty quote]
    LocalVar ix -> (! ix) . unLocals <$> ask
    GlobalVar (Rigid (RNameIntro (UserName name) _ did)) _ -> pure name
    GlobalVar name _ -> combine [pure "GLOBAL(", pretty name, pure ")"]
    UniVar (unGlobal -> n) ->
      lookupUV n >>= \case
        Just name -> pure name
        Nothing -> do
          name <- freshName
          modify(\st -> st { unUVNames = Map.insert n name (unUVNames st) })
          pure name
    Rigid TwoType -> pure "Bool"
    Rigid TwoIntro0 -> pure "true"
    Rigid TwoIntro1 -> pure "false"
    Rigid (SingType ty x) ->
      combine
        [ pure "["
        , pretty ty
        , pure " | "
        , pretty x
        , pure "]" ]
    Rigid (SingIntro x) -> pretty x
    Rigid (ObjIdType x y) -> con "Equal" [pretty x, pretty y]
    Rigid (ObjIdIntro _) -> pure "refl"
    Rigid (NameType univ ty) -> case univ of
      Obj -> con "Name" [pretty ty]
    Rigid (RNameIntro _ _ (Id n)) -> con "name" [pure . pack . show $ n]
    Rigid (CodeObjType ty) -> con "Code" [pretty ty]
    Rigid (CodeObjIntro code) -> combine [pure "<", pretty code, pure ">"]
    Rigid (ImplType p q) -> con "Implies" [pretty p, pretty q]
    Rigid (ConjType p q) -> con "And" [pretty p, pretty q]
    Rigid (DisjType p q) -> con "Or" [pretty p, pretty q]
    Rigid (AllType (MetaFunIntro body)) -> do
      name <- freshName
      combine [pure ("Forall " <> name <> ", "), bindLocal name (pretty body)]
    Rigid (SomeType (MetaFunIntro body)) -> do
      name <- freshName
      combine [pure ("Exists "  <> name <> ", "), bindLocal name (pretty body)]
    MetaTypeType -> pure "MetaType"
    ObjTypeType -> pure "Type"
    Rigid ElabError -> pure "<error>"
    Declare univ name ty cont ->
      let
        pre = case univ of
          Obj -> "[ p_declare "
          Meta -> "[ m_declare "
      in
        combine
          [ pure pre
          , pretty name
          , pure "\n"
          , indent <$> pretty ty
          , pure "\n"
          , indent <$> pretty cont
          , pure " ]" ]
    Define name def cont ->
      combine
        [ pure "[ define "
        , pretty name
        , pure "\n"
        , indent <$> pretty def
        , pure " "
        , indent <$> pretty cont
        , pure " ]"]
    Rigid TextType -> pure "Text"
    TextElimCat t1 t2 -> combine [pretty t1, pure " ++ ", pretty t2]
    (textIntro -> Just s) -> combine [pure "\"", pure . pack $ s, pure "\""]
    Rigid TextIntroNil -> pure "\"\""
    Rigid (TextIntroCons c t) -> combine [pure . pack $ '\"':c:"\" ++ ", pretty t]
    e -> pure . pack . show $ e

lookupUV :: Print sig m => Natural -> m (Maybe Text)
lookupUV n = do
  eqs <- unUVEqs <$> ask
  names <- unUVNames <$> get
  case Map.lookup n names of
    Just t -> pure (Just t)
    Nothing -> case Map.lookup n eqs of
      Just n' -> pure (Map.lookup n' names)
      Nothing -> pure Nothing

textIntro (Rigid TextIntroNil) = Just []
textIntro (Rigid (TextIntroCons c t)) = (c:) <$> textIntro t
textIntro _ = Nothing

con :: Print sig m => Text -> [m Text] -> m Text
con name args =
  combine
    [ pure name
    , pure "("
    , intercalate ", " <$> sequence args
    , pure ")" ]

combine :: Print sig m => [m Text] -> m Text
combine [] = pure ""
combine (a:as) = (<>) <$> a <*> combine as

bindManyLocals :: Print sig m => Seq Text -> m a -> m a
bindManyLocals Empty = id
bindManyLocals (t :<| ts) = bindLocal t . bindManyLocals ts

bindLocal :: Print sig m => Text -> m a -> m a
bindLocal var =
  local
    (\ctx -> ctx
      { unLocals = Map.insert 0 var (Map.mapKeys (+1) (unLocals ctx)) })

freshName :: Print sig m => m Text
freshName = do
  x <- unNextName <$> get
  modify (\st -> st { unNextName = unNextName st + 1 })
  pure (singleton (chr x))

prettyPure :: Map.Map Natural Natural -> Term -> Text
prettyPure eqs term =
  let
    (st, t) =
      run .
      runState (PrintState 97 mempty) .
      runReader (PrintContext mempty eqs) $
      pretty term
  in
    if null (unUVNames st) then
      t
    else
      let sep = if Data.Text.length t < 20 then " " else "\n  "
      in
        "forall " <>
        intercalate " " (fmap snd . Map.toList $  unUVNames st) <>
        "," <>
        sep <>
        t
