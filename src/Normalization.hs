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
import Data.Foldable.Extra
import Numeric.Natural
import GHC.Stack
import Extra
import Shower
import Debug.Trace
import Data.Sequence hiding(length, take)
import Prelude hiding(length)

data NormContext = NormContext
  { unEnv :: N.Environment
  , unVisited :: Set.Set Global
  , unTypeUVs :: Map.Map Global N.Term
  , unUVEqs :: Map.Map Global Global -- FIXME? `Map Global (Set Global)`
  , unDefEqs :: Seq (N.Term, N.Term) }
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
funIntros (C.MetaFunType _ _ outTy) = C.MetaFunIntro . funIntros outTy
funIntros (C.ObjFunType _ _ outTy) = C.ObjFunIntro . funIntros outTy
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

uvRedex :: Norm sig m => Global -> m (Maybe N.Term)
uvRedex gl = do
  visited <- unVisited <$> ask
  let !_ = ()--tracePrettyS "VIS" visited
  if Set.member gl visited then
    pure Nothing
  else do
    let !_ = ()--tracePretty "AAAAAAAAa"
    uvs <- unTypeUVs <$> ask
    case Map.lookup gl uvs of
      Just sol -> pure (Just sol)
      Nothing -> pure Nothing -- do
        -- let !_ = ()--tracePretty "BBBBBBBBBBBBBBB"
        -- eqs <- unUVEqs <$> ask
        -- let !_ = ()--tracePrettyS "EQS" eqs
        -- case Map.lookup gl eqs of
        --   Just gl' -> do
        --     -- a <- ask
        --     let !_ = ()--tracePretty ("CCCCCCCCCCCCCC", unVisited a, gl, gl')
        --     Just <$> local
        --       (\ctx -> ctx { unVisited = Set.insert gl' (unVisited ctx) })
        --       (eval (C.UniVar gl'))
        --   Nothing -> pure Nothing

-- gvRedex :: Norm sig m => Id -> m (Maybe N.Term)
-- gvRedex did = do
--   N.Env _ globals <- unEnv <$> ask
--   pure (Map.lookup did globals)

eval :: HasCallStack => Norm sig m => C.Term -> m N.Term
eval (C.MetaFunType pm inTy outTy) =
  N.MetaFunType pm <$> eval inTy <*> closureOf outTy
eval (C.MetaFunIntro body) = N.MetaFunIntro <$> closureOf body
eval (C.ObjFunType pm inTy outTy) =
  N.ObjFunType pm <$> eval inTy <*> closureOf outTy
eval (C.ObjFunIntro body) = N.ObjFunIntro <$> closureOf body
eval (C.ObjFunElim lam arg) = do
  vLam <- eval lam
  vArg <- eval arg
  let
    reded = do
      vLam <- unfold vLam
      case vLam of
        N.ObjFunIntro body -> Just <$> appClosure body vArg
        _ -> do
          r <- findDefEq vLam
          case r of
            Just (N.ObjFunIntro body) -> Just <$> appClosure body vArg
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
        _ -> do
          r <- findDefEq vLam
          case r of
            Just (N.MetaFunIntro body) -> Just <$> appClosure body vArg
            _ -> pure Nothing
  pure (N.Neutral reded (N.MetaFunElim vLam vArg))
eval (C.LocalVar ix) = entry ix
eval (C.GlobalVar did) = do
  vDid <- eval did
  unfold vDid >>= \vDid -> case N.viewName vDid of
    Just did' -> do
      N.Env _ ((! did') -> def) <- unEnv <$> ask
      pure (N.Neutral (pure (Just def)) (N.GlobalVar vDid))
    Nothing -> pure (N.Neutral (pure Nothing) (N.GlobalVar vDid))
eval (C.UniVar gl) = pure (N.Neutral (uvRedex gl) (N.UniVar gl))
eval (C.CodeObjElim term) = do
  vTerm <- eval term
  let
    reded = do
      vTerm <- unfold vTerm
      case vTerm of
        N.Rigid (N.CodeObjIntro code) -> pure (Just code)
        _ -> do
          r <- findDefEq vTerm
          case r of
            Just (N.Rigid (N.CodeObjIntro code)) -> pure (Just code)
            _ -> pure Nothing
  pure (N.Neutral reded (N.CodeObjElim vTerm))
eval (C.CodeCElim term) = do
  vTerm <- eval term
  let
    reded = do
      vTerm <- unfold vTerm
      case vTerm of
        N.Rigid (N.CodeCIntro code) -> pure (Just code)
        _ -> do
          r <- findDefEq vTerm
          case r of
            Just (N.Rigid (N.CodeCIntro code)) -> pure (Just code)
            _ -> pure Nothing
  pure (N.Neutral reded (N.CodeCElim vTerm))
eval (C.Rigid rterm) = N.Rigid <$> traverse eval rterm
eval (C.TwoElim scr body1 body2) = do
  vScr <- eval scr
  vBody1 <- eval body1
  vBody2 <- eval body2
  let
    reded = do
      vScr <- unfold vScr
      case vScr of
        N.Rigid N.TwoIntro0 -> pure (Just vBody1)
        N.Rigid N.TwoIntro1 -> pure (Just vBody2)
        _ -> do
          r <- findDefEq vScr
          -- let !_ = ()--tracePretty (vScr, vBody1, vBody2)
          -- !_ <- ()--tracePretty . unDefEqs <$> ask
          case r of
            Just (N.Rigid N.TwoIntro0) -> pure (Just vBody1)
            Just (N.Rigid N.TwoIntro1) -> pure (Just vBody2)
            _ -> pure Nothing
  pure (N.Neutral reded (N.TwoElim vScr vBody1 vBody2))
eval (C.SingElim scr) = do
  vScr <- eval scr
  let
    reded = do
      vScr <- unfold vScr
      case vScr of
        N.Rigid (N.SingIntro term) -> pure (Just term)
        _ -> do
          r <- findDefEq vScr
          case r of
            Just (N.Rigid (N.SingIntro term)) -> pure (Just term)
            _ -> pure Nothing
  pure (N.Neutral reded (N.SingElim vScr))
eval (C.RecElim str name) = do
  vStr <- eval str
  let
    reded = do
      vStr <- unfold vStr
      case vStr of
        N.RecIntro defs -> pure (snd <$> find (\(name', _) -> name == name') defs)
        _ -> do
          r <- findDefEq vStr
          case r of
            Just (N.RecIntro defs) ->
              pure (snd <$> find (\(name', _) -> name == name') defs)
            _ -> pure Nothing
  pure (N.Neutral reded (N.RecElim vStr name))
eval (C.RecIntro defs) = N.RecIntro <$> evalFields defs
eval (C.RecType tys) =
  N.RecType <$> traverse (\(fd, ty) -> (fd ,) <$> closureOf ty) tys
eval (C.Declare univ name ty cont) = do
  vName <- eval name
  vTy <- eval ty
  vCont <- eval cont
  pure (N.Neutral (pure (Just vCont)) (N.Declare univ vName vTy vCont))
eval (C.Define name def cont) = do
  vName <- eval name
  vDef <- eval def
  let
    reded = unfold vDef >>= \case
      N.Rigid (N.NameIntro _ did) ->
        Just <$> local (\ctx -> ctx { unEnv = N.withGlobal did vDef (unEnv ctx) }) (eval cont)
      _ -> pure Nothing
  vCont <- eval cont
  pure (N.Neutral reded (N.Define vName vDef vCont))

bindDefEq :: Norm sig m => N.Term -> N.Term -> m a -> m a
bindDefEq term1 term2 =
  local \ctx -> ctx { unDefEqs = (term1, term2) <| unDefEqs ctx }

findDefEq :: Norm sig m => N.Term -> m (Maybe N.Term)
findDefEq term = do
  defEqs <- unDefEqs <$> ask
  pure (fmap snd (find (\(e1, e2) -> e1 == term) defEqs))

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
readback' opt (N.MetaFunType pm inTy outTy) =
  C.MetaFunType pm <$>
    readback' opt inTy <*>
    bind (evalClosure outTy >>= readback' opt)
readback' opt (N.MetaFunIntro body) =
  C.MetaFunIntro <$>
    bind (evalClosure body >>= readback' opt)
readback' opt (N.ObjFunType pm inTy outTy) =
  C.ObjFunType pm <$>
    readback' opt inTy <*>
    bind (evalClosure outTy >>= readback' opt)
readback' opt (N.ObjFunIntro body) =
  C.ObjFunIntro <$>
    bind (evalClosure body >>= readback' opt)
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
readbackRedex opt (N.CodeObjElim quote) = C.CodeObjElim <$> readback' opt quote
readbackRedex opt (N.CodeCElim quote) = C.CodeCElim <$> readback' opt quote
readbackRedex opt (N.GlobalVar did) = C.GlobalVar <$> readback' opt did
readbackRedex opt (N.UniVar gl) = pure (C.UniVar gl)
readbackRedex opt (N.TwoElim scr body1 body2) =
  C.TwoElim <$>
    readback' opt scr <*>
    readback' opt body1 <*>
    readback' opt body2
readbackRedex opt (N.SingElim scr) = C.SingElim <$> readback' opt scr
readbackRedex opt (N.RecElim str name) = C.RecElim <$> readback' opt str <*> pure name
readbackRedex opt (N.Declare univ name ty cont) =
  C.Declare univ <$>
    readback' opt name <*>
    readback' opt ty <*>
    readback' opt cont
readbackRedex opt (N.Define name def cont) =
  C.Define <$>
    readback' opt name <*>
    readback' opt def <*>
    readback' opt cont

readback :: HasCallStack => Norm sig m => N.Term -> m C.Term
readback = readback' False

zonk :: HasCallStack => Norm sig m => N.Term -> m C.Term
zonk = readback' True

-- normalize :: HasCallStack => Norm sig m => N.Term -> m N.Term
-- normalize = readbackFull >=> eval
