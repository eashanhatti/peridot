module Elaboration.Query where

import Control.Monad.State
import Control.Monad.State.Class
import Control.Monad.Reader
import Control.Monad.Reader.Class
import Data.Map(Map, (!), insert)
import Syntax.Variable hiding (unId)
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
  { unMemoTable :: DHashMap Key Identity
  , unDecls :: Map Id DeclarationAst }

data QueryContext = QueryContext
  { unBindings :: Map Name Binding }

data Error = TooManyParams

data Binding = Local Index N.Term | Global Id

newtype Query a = Query (ReaderT QueryContext (State QueryState) a)
  deriving newtype (Functor, Applicative, Monad, MonadState QueryState, MonadReader QueryContext)

data Key a where
  ElabDecl :: Id -> Key C.Declaration

instance GEq Key where
  geq (ElabDecl _) (ElabDecl _) = Just Refl

instance Hashable (Some Key) where
  hashWithSalt salt (Some (ElabDecl did)) = salt `hashWithSalt` did

query :: Key a -> Query a
query key@(ElabDecl did) = do
  state <- get
  case DMap.lookup key (unMemoTable state) of
    Just (Identity decl) -> do
      put $ state { unMemoTable = DMap.insert key (Identity decl) (unMemoTable state) }
      pure decl
    Nothing -> ED.check (unDecls state ! did)

checkDecl :: Id -> Query C.Declaration
checkDecl did = query (ElabDecl did)

bindLocal :: Name -> N.Term -> Query a -> Query a
bindLocal name ty act =
  local
    (\ctx -> ctx { unBindings = insert name (Local (Index 0) ty) (fmap inc (unBindings ctx))})
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

addDecls :: [DeclarationAst] -> Query a -> Query a
addDecls [] act = act
addDecls (decl:decls) act = do
  state <- get
  put (state { unDecls = insert (unId decl) decl (unDecls state) })
  local
    (\ctx -> ctx { unBindings = insert (unDeclName decl) (Global (unId decl)) (unBindings ctx) })
    (addDecls decls act)

report :: Error -> Query ()
report _ = pure ()