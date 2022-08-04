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
import Extras
import Shower
import Debug.Trace
import Data.Sequence hiding(length)
import Prelude hiding(length, take)
import Data.Maybe
import Data.Text(pack)

data NormContext = NormContext
  { unEnv :: N.Environment
  , unVisited :: Set.Set Global
  , unTypeUVs :: Map.Map Global UVSolution
  , unUVEqs :: Map.Map Global (Set.Set Global)
  , unDefEqs :: Seq (N.Term, N.Term) }
  deriving (Show)

data UVSolution = UVSol
  { unCtx :: NormContext
  , unTerm :: N.Term }
  -- deriving (Show)
instance Show UVSolution where
  show (UVSol _ e) = "(UVSol (" ++ show e ++ "))"

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

-- closureOf :: HasCallStack => Norm sig m => C.Term -> m N.Closure
-- closureOf term = do
--   N.Env locals globals <- unEnv <$> ask
--   pure (N.Clo (N.Env (take (fromIntegral (maxIx term)) locals) globals) term)

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

-- delay :: Norm sig m => ReaderC NormContext Identity a -> m (ReaderC NormContext Identity a)
-- delay act = do
--   ctx <- ask
--   pure (local (\ctx' -> ctx { unTypeUVs = unTypeUVs ctx' }) act)

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
  if Set.member gl visited then
    pure Nothing
  else
    local
      (\ctx -> ctx { unVisited = Set.insert gl (unVisited ctx) })
      do
        uvs <- unTypeUVs <$> ask
        case Map.lookup gl uvs of
          Just (unTerm -> sol) -> pure (Just sol)
          Nothing -> do
            eqs <- unUVEqs <$> ask
            case Map.lookup gl eqs of
              Just gls -> do
                rs <- traverse uvRedex (Set.toList gls)
                case map fromJust . Prelude.filter isJust $ rs of
                  [e] -> pure (Just e)
                  _ -> pure Nothing
              Nothing -> pure Nothing

findUVSol :: Norm sig m => Global -> m (Maybe UVSolution)
findUVSol gl = do
  visited <- unVisited <$> ask
  if Set.member gl visited then
    pure Nothing
  else
    local
      (\ctx -> ctx { unVisited = Set.insert gl (unVisited ctx) })
      do
        uvs <- unTypeUVs <$> ask
        case Map.lookup gl uvs of
          Just sol -> pure (Just sol)
          Nothing -> do
            eqs <- unUVEqs <$> ask
            case Map.lookup gl eqs of
              Just gls -> do
                sols <- traverse findUVSol (Set.toList gls)
                case map fromJust . Prelude.filter isJust $ sols of
                  [sol] -> pure (Just sol)
                  _ -> pure Nothing
              Nothing -> pure Nothing

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
eval (C.ObjFunElim pm lam arg) = do
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
  pure (N.Neutral reded (N.ObjFunElim pm vLam vArg))
eval (C.MetaFunElim pm lam arg) = do
  vLam <- eval lam
  -- !_ <- tracePretty . N.unLocals . unEnv <$> ask
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
  pure (N.Neutral reded (N.MetaFunElim pm vLam vArg))
eval (C.LocalVar ix) = entry ix
eval (C.GlobalVar did sunf) = do
  vDid <- eval did
  unfold vDid >>= \vDid -> case N.viewName vDid of
    Just did' -> do
      N.Env _ ((Map.lookup did') -> def) <- unEnv <$> ask
      pure (N.Neutral (pure def) (N.GlobalVar vDid sunf))
    Nothing -> pure (N.Neutral (pure Nothing) (N.GlobalVar vDid sunf))
eval (C.UniVar gl ty) = do
  vTy <- traverse eval ty
  pure (N.Neutral (uvRedex gl) (N.UniVar gl vTy))
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
eval (C.TextElimCat t1 t2) = do
  vT1 <- eval t1
  vT2 <- eval t2
  let
    reded = do
      -- vT1' <- eval t1
      -- vT2' <- eval t2
      -- Just <$> go vT1' vT2'
      Just <$> go vT1 vT2
  pure (N.Neutral reded (N.TextElimCat vT1 vT2))
  where
    go :: Norm sig m => N.Term -> N.Term -> m N.Term
    go t1@(N.Neutral r _) t2 = do
      r <- force r
      case r of
        Just r -> go r t2
        Nothing -> pure (N.Neutral (pure Nothing) (N.TextElimCat t1 t2))
    go (N.Rigid (N.TextIntroCons c t1)) t2 = N.Rigid . N.TextIntroCons c <$> go t1 t2
    go (N.Rigid N.TextIntroNil) t2 = pure t2
    go e1 e2 = pure (N.Neutral (pure Nothing) (N.TextElimCat e1 e2))
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
        N.RecIntro defs -> do
          vDefs <- evalFieldClos Empty defs
          pure (snd <$> find (\(name', _) -> name == name') vDefs)
        _ -> do
          r <- findDefEq vStr
          case r of
            Just (N.RecIntro defs) -> do
              vDefs <- evalFieldClos Empty defs
              pure (snd <$> find (\(name', _) -> name == name') vDefs)
            _ -> pure Nothing
  pure (N.Neutral reded (N.RecElim vStr name))
eval (C.RecIntro defs) =
  N.RecIntro <$> (traverse (\(fd, def) -> (fd ,) <$> closureOf def) defs)
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

data ReadbackDepth = None | Zonk | Full

notNone None = False
notNone _ = True

readback' ::
  forall sig m. HasCallStack => Norm sig m =>
  ReadbackDepth ->
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
  if lvl > N.envSize env || N.envSize env - lvl < 1 then
    -- error ("BUG: Local variable readback " ++ show (lvl, N.envSize env, 1))
    pure (C.Rigid (C.Dummy (pack . show $ (lvl, N.envSize env, 1))))
  else
    pure (C.LocalVar (Index (N.envSize env - lvl - 1)))
readback' opt e@(N.Neutral sol redex) = do
  vSol <- force sol
  case (opt, vSol, redex) of
    (notNone -> True, Just vSol, N.UniVar gl _) -> do
      sol <- findUVSol gl
      case sol of
        Just (unCtx -> lCtx) ->
          local
            (\ctx -> lCtx
              { unTypeUVs = unTypeUVs ctx
              , unUVEqs = unUVEqs ctx })
            (readback' opt vSol)
        Nothing -> error "TODO: Error reporting"
    (Full, Just vSol, _) -> readback' Full vSol
    -- (True, Nothing, N.UniVar gl) -> error $ "UNSOLVED VAR " ++ show gl
    _ -> readbackRedex opt redex
readback' opt (N.RecIntro defs) = do
  vDefs <- evalFieldClos Empty defs
  cDefs <-
    traverseWithIndex
      (\i (fd, def) -> (fd ,) <$> bindN i (readback' opt def))
      vDefs
  pure (C.RecIntro cDefs)
readback' opt (N.RecType tys) = do
  vTys <- evalFieldClos Empty tys
  cTys <-
    traverseWithIndex
      (\i (fd, ty) -> (fd ,) <$> bindN i (readback' opt ty))
      vTys
  pure (C.RecType cTys)
readback' opt (N.Rigid rterm) = C.Rigid <$> traverse (readback' opt) rterm

evalFieldClos ::
  HasCallStack => Norm sig m =>
  Seq N.Term ->
  Seq (Field, N.Closure) ->
  m (Seq (Field, N.Term))
evalFieldClos _ Empty = pure Empty
evalFieldClos defs ((fd, ty) :<| tys) = do
  vTy <- appClosureN ty defs
  l <- level
  vTys <- bind (evalFieldClos (N.LocalVar l <| defs) tys)
  pure ((fd, vTy) <| vTys)

readbackRedex :: HasCallStack => Norm sig m => ReadbackDepth -> N.Redex -> m C.Term
readbackRedex opt (N.MetaFunElim pm lam arg) =
  C.MetaFunElim pm <$>
    readback' opt lam <*>
    readback' opt arg
readbackRedex opt (N.ObjFunElim pm lam arg) =
  C.ObjFunElim pm <$>
    readback' opt lam <*>
    readback' opt arg
readbackRedex opt (N.CodeObjElim quote) = C.CodeObjElim <$> readback' opt quote
readbackRedex opt (N.GlobalVar did sunf) = flip C.GlobalVar sunf <$> readback' opt did
readbackRedex opt (N.UniVar gl ty) = C.UniVar gl <$> traverse (readback' opt) ty
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
readbackRedex opt (N.TextElimCat t1 t2) =
  C.TextElimCat <$> readback' opt t1 <*> readback' opt t2

readback :: HasCallStack => Norm sig m => N.Term -> m C.Term
readback = readback' None

zonk :: HasCallStack => Norm sig m => N.Term -> m C.Term
zonk = readback' Zonk

normalize :: Norm sig m => N.Term -> m C.Term
normalize = readback' Full
