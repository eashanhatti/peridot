module Elaboration.Query where

import Control.Monad.State
import Control.Monad.State.Class
import Control.Monad.Reader
import Control.Monad.Reader.Class
import Data.Map(Map, (!), insert)
import Syntax.Variable
import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Telescope qualified as T
import Syntax.Surface
import Data.Some
import Elaboration.Decl qualified as ED
import Data.Dependent.HashMap qualified as DMap
import Data.Dependent.HashMap(DHashMap)
import Data.Functor.Identity
import Data.GADT.Compare
import Data.Type.Equality
import Data.Hashable
import GHC.Generics

data QueryState = QueryState
  { memoTable :: DHashMap Key Identity
  , decls :: Map Id DeclarationAst }

data QueryContext = QueryContext
  { bindings :: Map Name Binding }

data Error = TooManyParams

data Binding = Local Index N.Term | Global Id N.Term

newtype Query a = Query (ReaderT QueryContext (State QueryState) a)
  deriving newtype (Functor, Applicative, Monad, MonadState QueryState, MonadReader QueryContext)

data Key a where
  ElabDecl :: Id -> Key C.Declaration

instance GEq Key where
  geq (ElabDecl _) (ElabDecl _) = Just Refl

instance Hashable (Some Key) where
  hashWithSalt salt (Some (ElabDecl did)) = salt `hashWithSalt` did

bindLocal :: Name -> N.Term -> Query a -> Query a
bindLocal name ty act =
  local
    (\ctx -> ctx { bindings = insert name (Local (Index 0) ty) (fmap inc (bindings ctx))})
    act
  where
    inc (Local ix ty) = Local (ix + 1) ty
    inc b = b

bindAll :: N.Telescope -> [Name] -> Query a -> Query a
bindAll T.Empty _ act = act
bindAll (T.Bind ty tele) (name:names) act = bindLocal name ty (bindAll tele names act)
bindAll _ [] act = do
  report TooManyParams
  act

report :: Error -> Query ()
report _ = pure ()

checkDecl :: Id -> Query C.Declaration
checkDecl did = query (ElabDecl did)

query :: Key a -> Query a
query key@(ElabDecl did) = do
  state <- get
  case DMap.lookup key (memoTable state) of
    Just (Identity decl) -> do
      put $ state { memoTable = DMap.insert key (Identity decl) (memoTable state) }
      pure decl
    Nothing -> ED.check (decls state ! did)