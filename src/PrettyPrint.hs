module PrettyPrint where

import Control.Algebra
import Control.Effect.Reader(Reader, ask, local)
import Control.Carrier.Reader
import Control.Effect.State(State, get, put, modify)
import Control.Carrier.State.Strict
import Syntax.Core
import Data.Text hiding(zip, foldl')
import Data.Map qualified as Map
import Syntax.Common(Id(..), Index(..))
import Data.Char
import Control.Monad
import Prelude hiding(zip, foldl', intercalate, words)
import Data.Foldable
import Data.Sequence hiding(singleton, foldl', replicateM)
import Extra

data PrintContext = PrintContext
  { unLocals :: Map.Map Index Text }

data PrintState = PrintState
  { unNextName :: Int }

type Print sig m =
  ( Has (Reader PrintContext) sig m
  , Has (State PrintState) sig m )

prettyPPm :: PassMethod -> Text
prettyPPm Unification = "inferred "
prettyPPm Explicit = ""

pretty :: Print sig m => Term -> m Text
pretty term =
  case term of
    (viewObjFunTys -> (inTys@(_:<|_), outTy)) -> do
      names <- traverse (const freshName) inTys
      params <-
        traverse
          (\(name, (pm, inTy)) -> ((prettyPPm pm <> name <> " : ") <>) <$> pretty inTy)
          (zip names inTys)
      tOutTy <- bindManyLocals names (pretty outTy)
      pure ("Function(" <> intercalate ", " (toList params) <> ") -> " <> tOutTy)
    (viewMetaFunTys -> (inTys@(_:<|_), outTy)) -> do
      names <- traverse (const freshName) inTys
      params <-
        traverse
          (\(name, (pm, inTy)) -> ((prettyPPm pm <> name <> " : ") <>) <$> pretty inTy)
          (zip names inTys)
      tOutTy <- bindManyLocals names (pretty outTy)
      pure ("Function(" <> intercalate ", " (toList params) <> ") ~> " <> tOutTy)
    (viewObjFunIntros -> (n@((> 0) -> True), body)) -> do
      names <- replicateM (fromIntegral n) freshName
      (("function(" <> intercalate ", " names <> ") => ") <>) <$> bindManyLocals (fromList names) (pretty body)
    TwoElim scr body1 body2 ->
      combine [pure "if ", pretty scr, pure " { ", pretty body1, pure " } else { ", pretty body2]
    RecType tys -> do
      tTys <- traverse (\(fd, ty) -> ((unField fd <> " : ") <>) <$> pretty ty) tys
      pure ("Record { " <> intercalate ", " (toList tTys) <> " }")
    RecIntro defs -> do
      tDefs <- traverse (\(fd, def) -> ((unField fd <> " = ") <>) <$> pretty def) defs
      pure ("record { " <> intercalate ", " (toList tDefs) <> " }")
    RecElim str fd -> combine [pretty str, pure ("." <> unField fd)]
    SingElim sing -> pretty sing
    (viewFunElims -> (lam, args@(_:<|_))) -> do
      tLam <- pretty lam
      let
        tLam' =
          case words tLam of
            _:[] -> tLam
            _:_ -> "(" <> tLam <> ")"
      combine [pure tLam', pure "(", intercalate ", " . toList <$> traverse pretty args, pure ")"]
    CodeObjElim quote -> combine [pure "~", pretty quote]
    CodeCElim quote -> combine [pure "c~", pretty quote]
    LocalVar ix -> (Map.! ix) . unLocals <$> ask
    GlobalVar (Rigid (RNameIntro (UserName name) _ did)) -> pure name
    GlobalVar name -> combine [pure "GLOBAL(", pretty name, pure ")"]
    UniVar (LVGlobal n) -> pure ("?" <> pack (show n))
    UniVar (UVGlobal n) -> pure ("?" <> pack (show n))
    Rigid TwoType -> pure "Bool"
    Rigid TwoIntro0 -> pure "true"
    Rigid TwoIntro1 -> pure "false"
    Rigid (SingType ty x) -> combine [pure "[ ", pretty ty, pure " | ", pretty x, pure " ]"]
    Rigid (SingIntro x) -> pretty x
    Rigid (ObjIdType x y) -> con "Equals" [pretty x, pretty y]
    Rigid (ObjIdIntro _) -> pure "reflexive"
    Rigid (NameType univ ty) -> case univ of
      Obj -> con "PName" [pretty ty]
      LowC -> con "CName" [pretty ty]
    Rigid (CodeObjType ty) -> con "Code" [pretty ty]
    Rigid (CodeObjIntro code) -> combine [pure "<", pretty code, pure ">"]
    Rigid (CodeCType ty) -> con "CCode" [pretty ty]
    Rigid (CodeCIntro code) -> combine [pure "c<", pretty code, pure ">"]
    Rigid (ImplType p q) -> combine [pretty p, pure "⊃", pretty q]
    Rigid (ConjType p q) -> combine [pretty p, pure "∧", pretty q]
    Rigid (DisjType p q) -> combine [pretty p, pure "∨", pretty q]
    Rigid (AllType (MetaFunIntro body)) -> do
      name <- freshName
      combine [pure ("∀" <> name <> ", "), bindLocal name (pretty body)]
    Rigid (SomeType (MetaFunIntro body)) -> do
      name <- freshName
      combine [pure ("∃" <> name <> ", "), bindLocal name (pretty body)]
    MetaTypeType -> pure "MetaType"
    ObjTypeType -> pure "Type"
    LowCTypeType -> pure "CType"
    Rigid ElabError -> pure "\ESC[31mERROR\ESC[0m"

con :: Print sig m => Text -> [m Text] -> m Text
con name args = combine [pure name, pure "(", intercalate ", " <$> sequence args, pure ")"]

combine :: Print sig m => [m Text] -> m Text
combine [] = pure ""
combine (a:as) = (<>) <$> a <*> combine as

bindManyLocals :: Print sig m => Seq Text -> m a -> m a
bindManyLocals Empty = id
bindManyLocals (t :<| ts) = bindLocal t . bindManyLocals ts

bindLocal :: Print sig m => Text -> m a -> m a
bindLocal var = local (\ctx -> ctx { unLocals = Map.insert 0 var (Map.mapKeys (+1) (unLocals ctx)) })

freshName :: Print sig m => m Text
freshName = do
  x <- unNextName <$> get
  modify (\st -> st { unNextName = unNextName st + 1 })
  pure (singleton (chr x))

prettyPure :: Term -> Text
prettyPure term =
  run .
  runReader (PrintContext mempty) .
  evalState (PrintState 97) $
  pretty term