module Normalization where

import Syntax.Core qualified as C
import Syntax.Semantic qualified as N
import Syntax.Common
import Control.Monad
import Control.Effect.Reader
import Control.Carrier.Reader
import Control.Effect.State
import Control.Carrier.State.Strict
import Control.Algebra(Has, run)
import Data.Set qualified as Set
import Data.Map qualified as Map
import Data.Foldable
import Data.Functor.Identity
import Numeric.Natural
import GHC.Stack
import Extra
import Shower
import Debug.Trace
import Data.Sequence hiding(length)
import Prelude hiding(length)

data NormContext = NormContext
  { unEnv :: N.Environment
  , unVisited :: Set.Set Global
  , unTypeUVs :: Map.Map Global N.Term
  -- , unVCUVs :: Map.Map Global N.ValueCategory
  , unUVEqs :: Map.Map Global Global } -- FIXME? `Map Global (Set Global)`
  deriving (Show)

type Norm sig m =
  ( Has (Reader NormContext) sig m )

bind :: HasCallStack => Norm sig m => m a -> m a
bind = local (\ctx -> ctx
  { unEnv =
    N.withLocal
      (N.LocalVar (fromIntegral (N.envSize (unEnv ctx))))
      (unEnv ctx) })

bindN :: HasCallStack => Norm sig m => Int -> m a -> m a
bindN 0 = id
bindN n = bind . bindN (n - 1)

define :: HasCallStack => Norm sig m => N.Term -> m a -> m a
define def = local (\ctx -> ctx { unEnv = N.withLocal def (unEnv ctx) })

closureOf :: HasCallStack => Norm sig m => C.Term -> m N.Closure
closureOf term = do
  env <- unEnv <$> ask
  pure (N.Clo env term)

appClosure :: HasCallStack => Norm sig m => N.Closure -> N.Term -> m N.Term
appClosure clo arg = appClosureN clo (singleton arg)

appClosureN :: HasCallStack => Norm sig m => N.Closure -> Seq N.Term -> m N.Term
appClosureN (N.Clo env body) args =
  local (\ctx -> ctx { unEnv = foldr N.withLocal env args }) (eval body)

evalClosure :: HasCallStack => Norm sig m => N.Closure -> m N.Term
evalClosure clo@(N.Clo env _) =
  appClosure
    clo
    (N.LocalVar (fromIntegral (N.envSize env)))

funIntros :: C.Term -> (C.Term -> C.Term)
funIntros (C.MetaFunType _ outTy) = C.MetaFunIntro . funIntros outTy
funIntros (C.ObjFunType _ outTy) = C.ObjFunIntro . funIntros outTy
funIntros _ = id

level :: Norm sig m => m Level
level = fromIntegral . N.envSize . unEnv <$> ask

force :: Norm sig m => ReaderC NormContext Identity a -> m a
force act = do
  ctx <- ask
  pure (run . runReader ctx $ act)

unfold :: Norm sig m => N.Term -> m N.Term
unfold n@(N.Neutral term redex) = do
  term <- force term
  case term of
    Just term -> unfold term
    Nothing -> pure n
unfold term = pure term

definition :: C.Declaration -> C.Term
definition (C.MetaConst did sig) = funIntros sig (C.Rigid (C.MetaConstIntro did))
definition (C.ObjTerm _ _ def) = def
definition (C.MetaTerm _ _ def) = def
definition (C.DElabError) = C.Rigid C.ElabError

uvRedex :: Norm sig m => Global -> m (Maybe N.Term)
uvRedex gl = do
  visited <- unVisited <$> ask
  if Set.member gl visited then
    pure Nothing
  else do
    uvs <- unTypeUVs <$> ask
    case Map.lookup gl uvs of
      Just sol -> pure (Just sol)
      Nothing -> do
        eqs <- unUVEqs <$> ask
        case Map.lookup gl eqs of
          Just gl' -> Just <$> eval (C.UniVar gl')
          Nothing -> pure Nothing

-- gvRedex :: Norm sig m => Id -> m (Maybe N.Term)
-- gvRedex did = do
--   N.Env _ globals <- unEnv <$> ask
--   pure (Map.lookup did globals)

eval :: HasCallStack => Norm sig m => C.Term -> m N.Term
eval (C.MetaFunType inTy outTy) = N.MetaFunType <$> eval inTy <*> closureOf outTy
eval (C.MetaFunIntro body) = N.MetaFunIntro <$> closureOf body
eval (C.ObjFunType inTy outTy) = N.ObjFunType <$> eval inTy <*> closureOf outTy
eval (C.ObjFunIntro body) = N.ObjFunIntro <$> closureOf body
eval (C.ObjFunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  let
    reded = do
      vLam <- unfold vLam
      case vLam of
        N.ObjFunIntro body -> Just <$> appClosure body vArg
        _ -> pure Nothing
  pure (N.Neutral reded (N.ObjFunElim vLam vArg))
eval (C.MetaFunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  let
    reded = do
      vLam <- unfold vLam
      case vLam of
        N.MetaFunIntro body -> Just <$> appClosure body vArg
        _ -> pure Nothing
  pure (N.Neutral reded (N.MetaFunElim vLam vArg))
eval (C.TypeType (C.SUniVar gl)) = undefined -- FIXME?
eval (C.TypeType C.Meta) = pure (N.TypeType N.Meta)
eval (C.TypeType C.Obj) = pure (N.TypeType N.Obj)
eval (C.TypeType (C.Low l)) = pure (N.TypeType (N.Low l))
eval (C.LocalVar ix) = entry ix
eval (C.GlobalVar did) = do
  N.Env _ ((! did) -> def) <- unEnv <$> ask
  pure (N.Neutral (pure (Just def)) (N.GlobalVar did))
eval (C.UniVar gl) = pure (N.Neutral (uvRedex gl) (N.UniVar gl))
eval (C.CodeCoreElim term) = do
  vTerm <- eval term
  let
    reded =
      case vTerm of
        N.Rigid (N.CodeCoreIntro code) -> Just code
        _ -> Nothing
  pure (N.Neutral (pure reded) (N.CodeCoreElim vTerm))
eval (C.CodeLowCTmElim term) = do
  vTerm <- eval term
  let
    reded =
      case vTerm of
        N.Rigid (N.CodeLowCTmIntro code) -> Just code
        _ -> Nothing
  pure (N.Neutral (pure reded) (N.CodeLowCTmElim vTerm))
eval (C.Rigid rterm) = N.Rigid <$> traverse eval rterm
eval (C.Let decls body) = do
  let defs = fmap (\decl -> (C.unId decl, definition decl)) decls
  vDefs <- traverse (\(did, def) -> eval def >>= pure . (did,)) defs
  let
    reded =
      local
        (\ctx -> ctx { unEnv = withGlobals vDefs (unEnv ctx) })
        (eval body)
  vDecls <- traverse (traverse eval) decls
  vBody <- eval body
  pure (N.Neutral (Just <$> reded) (N.Let vDecls vBody))
eval (C.TwoElim scr ty body1 body2) = do
  vScr <- eval scr
  tyClo <- closureOf ty
  vBody1 <- eval body1
  vBody2 <- eval body2
  let
    reded =
      case vScr of
        N.Rigid N.TwoIntro0 -> Just vBody1
        N.Rigid N.TwoIntro1 -> Just vBody2
        _ -> Nothing
  pure (N.Neutral (pure reded) (N.TwoElim vScr tyClo vBody1 vBody2))
eval (C.SingElim scr) = do
  vSrc <- eval scr
  let
    reded =
      case vSrc of
        N.Rigid (N.SingIntro term) -> Just term
        _ -> Nothing
  pure (N.Neutral (pure reded) (N.SingElim vSrc))
eval (C.RecElim str name) = do
  vStr <- eval str
  let
    reded =
      case vStr of
        N.RecIntro defs -> snd <$> find (\(name', _) -> name == name') defs
        _ -> Nothing
  pure (N.Neutral (pure reded) (N.RecElim vStr name))
eval (C.RecIntro defs) = N.RecIntro <$> evalFields defs
eval (C.RecType tys) =
  N.RecType <$> traverse (\(fd, ty) -> (fd ,) <$> closureOf ty) tys

evalFields :: Norm sig m => Seq (Field, C.Term) -> m (Seq (Field, N.Term))
evalFields Empty = pure Empty
evalFields ((name, fd) :<| fds) = do
  vFd <- eval fd
  fds' <- define vFd (evalFields fds)
  pure ((name, vFd) <| fds')

withGlobals :: Seq (Id, N.Term) -> N.Environment -> N.Environment
withGlobals defs (N.Env locals globals) =
  let globals' = foldl' (\acc (did, def) -> Map.insert did def acc) globals defs
  in N.Env locals globals'

entry :: HasCallStack => Norm sig m => Index -> m N.Term
entry ix = do
  N.Env locals _ <- unEnv <$> ask
  if fromIntegral ix >= length locals then
    error $ "`entry`:" ++ shower (ix, locals)
  else
    pure (locals `index` fromIntegral ix)

type ShouldZonk = Bool

readback' ::
  forall sig m. HasCallStack => Norm sig m =>
  ShouldZonk ->
  N.Term ->
  m C.Term
readback' opt (N.MetaFunType inTy outTy) =
  C.MetaFunType <$>
    readback' opt inTy <*>
    bind (evalClosure outTy >>= readback' opt)
readback' opt (N.MetaFunIntro body) =
  C.MetaFunIntro <$>
    bind (evalClosure body >>= readback' opt)
readback' opt (N.ObjFunType inTy outTy) =
  C.ObjFunType <$>
    readback' opt inTy <*>
    bind (evalClosure outTy >>= readback' opt)
readback' opt (N.ObjFunIntro body) =
  C.ObjFunIntro <$>
    bind (evalClosure body >>= readback' opt)
readback' opt (N.TypeType (N.SUniVar gl)) = undefined -- FIXME?
readback' opt (N.TypeType (N.Low l)) = pure (C.TypeType (C.Low l))
readback' opt (N.TypeType N.Meta) = pure (C.TypeType C.Meta)
readback' opt (N.TypeType N.Obj) = pure (C.TypeType C.Obj)
readback' opt (N.LocalVar (Level lvl)) = do
  env <- unEnv <$> ask
  pure (C.LocalVar (Index (fromIntegral (N.envSize env) - lvl - 1)))
readback' opt (N.Neutral sol redex) = do
  vSol <- force sol
  case (opt, vSol, redex) of
    (True, Just vSol, N.UniVar _) -> readback' True vSol
    -- (True, Nothing, N.UniVar gl) -> error $ "UNSOLVED VAR " ++ show gl
    _ -> readbackRedex opt redex
readback' opt (N.RecIntro fds) =
  C.RecIntro <$> traverse (\(fd, def) -> (fd ,) <$> readback' opt def) fds
readback' opt (N.RecType tys) = do
  vTys <- evalFieldTypes Empty tys
  cTys <-
    traverseWithIndex
      (\i (fd, ty) -> (fd ,) <$> bindN i (readback' opt ty))
      vTys
  pure (C.RecType cTys)
readback' opt (N.Rigid rterm) = C.Rigid <$> traverse (readback' opt) rterm

evalFieldTypes ::
  HasCallStack => Norm sig m =>
  Seq N.Term ->
  Seq (Field, N.Closure) ->
  m (Seq (Field, N.Term))
evalFieldTypes _ Empty = pure Empty
evalFieldTypes defs ((fd, ty) :<| tys) = do
  vTy <- appClosureN ty defs
  l <- level
  vTys <- bind (evalFieldTypes (N.LocalVar l <| defs) tys)
  pure ((fd, vTy) <| vTys)

readbackRedex :: HasCallStack => Norm sig m => ShouldZonk -> N.Redex -> m C.Term
readbackRedex opt (N.MetaFunElim lam arg) =
  C.MetaFunElim <$>
    readback' opt lam <*>
    readback' opt arg
readbackRedex opt (N.ObjFunElim lam arg) =
  C.ObjFunElim <$>
    readback' opt lam <*>
    readback' opt arg
readbackRedex opt (N.CodeCoreElim quote) = C.CodeCoreElim <$> readback' opt quote
readbackRedex opt (N.CodeLowCTmElim quote) = C.CodeLowCTmElim <$> readback' opt quote
readbackRedex opt (N.GlobalVar did) = pure (C.GlobalVar did)
readbackRedex opt (N.UniVar gl) = pure (C.UniVar gl)
readbackRedex opt (N.Let decls body) =
  C.Let <$>
    traverse (traverse (readback' opt)) decls <*>
    readback' opt body
readbackRedex opt (N.TwoElim scr ty body1 body2) =
  C.TwoElim <$>
    readback' opt scr <*>
    (evalClosure ty >>= readback' opt) <*>
    readback' opt body1 <*>
    readback' opt body2
readbackRedex opt (N.SingElim scr) = C.SingElim <$> readback' opt scr
readbackRedex opt (N.RecElim str name) = C.RecElim <$> readback' opt str <*> pure name

readback :: HasCallStack => Norm sig m => N.Term -> m C.Term
readback = readback' False

zonk :: HasCallStack => Norm sig m => N.Term -> m C.Term
zonk = readback' True

-- normalize :: HasCallStack => Norm sig m => N.Term -> m N.Term
-- normalize = readbackFull >=> eval
