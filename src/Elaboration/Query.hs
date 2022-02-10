module Elaboration.Query where

import Control.Effect.State(State, get, put)
import Control.Effect.Reader(Reader, ask, local)
import Control.Algebra(Has)
import Data.Map(Map, (!), insert)
import Syntax.Variable hiding (unId)
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Telescope qualified as T
import Elaboration.Decl as ED
import Syntax.Surface
import Data.Some
import Data.Dependent.HashMap qualified as DMap
import Data.Dependent.HashMap(DHashMap)
import Data.Functor.Identity
import Data.GADT.Compare
import Data.Type.Equality
import Data.Hashable
import GHC.Generics
import Normalization

data QueryState = QueryState
  { unMemoTable :: DHashMap Key Identity
  , unDecls :: Map Id DeclarationAst }

data QueryContext = QueryContext
  { unBindings :: Map Name Binding }

data Error = TooManyParams

data Binding = LocalB Index N.Term | GlobalB Id

type Query sig m = (Has (Reader QueryContext) sig m, Has (State QueryState) sig m, Norm sig m)

data Key a where
  ElabDecl :: Id -> Key C.Declaration

instance GEq Key where
  geq (ElabDecl _) (ElabDecl _) = Just Refl

instance Hashable (Some Key) where
  hashWithSalt salt (Some (ElabDecl did)) = salt `hashWithSalt` did

query :: Query sig m => Key a -> m a
query key@(ElabDecl did) = do
  state <- get
  case DMap.lookup key (unMemoTable state) of
    Just (Identity decl) -> do
      put $ state { unMemoTable = DMap.insert key (Identity decl) (unMemoTable state) }
      pure decl
    Nothing -> ED.check (unDecls state ! did)

bindLocalB :: Query sig m => Name -> N.Term -> m a -> m a
bindLocalB name ty act =
  local
    (\ctx -> ctx { unBindings = insert name (LocalB (Index 0) ty) (fmap inc (unBindings ctx))})
    act
  where
    inc (LocalB ix ty) = LocalB (ix + 1) ty
    inc b = b

bindAll :: Query sig m => N.Telescope -> [Name] -> m a -> m a
bindAll T.Empty _ act = act
bindAll (T.Bind ty tele) (name:names) act = bindLocalB name ty (bindAll tele names act)
bindAll _ [] act = do
  report TooManyParams
  act

addDecls :: Query sig m => [DeclarationAst] -> m a -> m a
addDecls [] act = act
addDecls (decl:decls) act = do
  state <- get
  put (state { unDecls = insert (unId decl) decl (unDecls state) })
  local
    (\ctx -> ctx { unBindings = insert (unDeclName decl) (GlobalB (unId decl)) (unBindings ctx) })
    (addDecls decls act)

report :: Query sig m => Error -> m ()
report _ = pure ()