{-# LANGUAGE LambdaCase #-}
-- {-# OPTIONS_GHC -fdefer-type-errors #-}

module Unification where

import qualified Data.Map as Map
import qualified Norm as N
import qualified Core as C
import Var
import Data.List(uncons)
import Data.Maybe(fromJust)
import Data.Functor.Identity(Identity)
import Control.Monad.State(State, state, runState)
import Control.Monad.Reader(runReader)
import Control.Monad.Except(ExceptT, lift, throwError, liftEither, runExceptT)
import Control.Monad(ap, liftM)
import qualified Data.Set as Set

data Error = InvalidSpine | OccursCheck | EscapingVar | Mismatch N.Value N.Value | MismatchStages C.Stage C.Stage

instance Show Error where
  show e = case e of
    InvalidSpine -> "Invalid Spine"
    OccursCheck -> "Failed Occurs Check"
    EscapingVar -> "Escaping Var"
    Mismatch val val' -> "Mismatched Types:\n  " ++ show val ++ "\n  " ++ show val'
    MismatchStages s s' -> "Mismatched Stages: " ++ show s ++ ", " ++ show s'

newtype Unify a = Unify (State (N.Metas, N.StageMetas, [Error]) a)

instance Functor Unify where
  fmap = liftM

instance Applicative Unify where
  pure a = Unify $ state $ \s -> (a, s)
  (<*>) = ap

instance Monad Unify where
  return a = Unify $ state $ \s -> (a, s)
  (Unify act) >>= k = Unify $ state $ \s ->
    let
      (a, s') = runState act s
      (Unify act') = (k a)
    in runState act' s'

get :: Unify (N.Metas, N.StageMetas, [Error])
get = Unify $ state $ \s -> (s, s)

put :: (N.Metas, N.StageMetas, [Error]) -> Unify ()
put s = Unify $ state $ \_ -> ((), s)

runUnify :: Unify a -> (N.Metas, N.StageMetas, [Error]) -> (a, (N.Metas, N.StageMetas, [Error]))
runUnify (Unify act) s = runState act s

runNorm :: Level -> N.Norm a -> Unify a
runNorm lv act = do
  (metas, _, _) <- get
  pure $ runReader act (lv, metas, Set.singleton C.T, [])

putSolution :: Global -> N.Value -> Unify ()
putSolution gl sol = do
  (metas, stageMetas, probs) <- get
  put (Map.insert gl (N.Solved sol) metas, stageMetas, probs)

putStageSolution :: Global -> C.Stage -> Unify ()
putStageSolution gl sol = do
  (metas, stageMetas, probs) <- get
  put (metas, Map.insert gl (N.Solved sol) stageMetas, probs)

putError :: Error -> Unify ()
putError err = do
  (metas, stageMetas, errors) <- get
  put (metas, stageMetas, err:errors)

-- force :: N.Value -> Unify N.Value
-- force val = do
--   (metas, _, _) <- get
--   runNorm $ N.force val

getMetas :: Unify N.Metas
getMetas = do
  (metas, _, _) <- get
  pure metas

data PartialRenaming = PartialRenaming
  { domain :: Level
  , codomain :: Level
  , ren :: Map.Map Level Level }

inc :: PartialRenaming -> PartialRenaming
inc pren = PartialRenaming
  (Level $ unLevel (domain pren) + 1)
  (Level $ unLevel (codomain pren) + 1)
  (Map.insert (codomain pren) (domain pren) (ren pren))

invert :: N.Metas -> Level -> N.Spine -> ExceptT Error Unify PartialRenaming
invert metas gamma spine = do
  let go :: N.Spine -> ExceptT Error Unify (Level, Map.Map Level Level)
      go = \case
        (arg:spine) -> do
          (domain, ren) <- go spine
          arg <- lift $ runNorm gamma $ N.force arg
          case arg of
            N.StuckRigidVar _ lv [] | Map.notMember lv ren -> liftEither $ Right (Level $ unLevel domain + 1, Map.insert lv domain ren)
            _ -> throwError InvalidSpine
        [] -> liftEither $ Right (Level 0, mempty)
  (domain, ren) <- go spine
  liftEither $ Right $ PartialRenaming domain gamma ren

rename :: N.Metas -> Global -> PartialRenaming -> N.Value -> ExceptT Error Unify C.Term
rename metas gl pren rhs = go pren rhs
  where
    goSpine :: PartialRenaming -> C.Term -> N.Spine -> ExceptT Error Unify C.Term
    goSpine pren val spine = case spine of
      (arg:spine) -> C.FunElim <$> goSpine pren val spine <*> go pren arg
      [] -> liftEither $ Right val

    goTerm :: PartialRenaming -> C.Term -> ExceptT Error Unify C.Term
    goTerm pren trm = undefined

    go :: PartialRenaming -> N.Value -> ExceptT Error Unify C.Term
    go pren val = do
      val <- lift $ runNorm (domain pren) $ N.force val
      case val of
        N.StuckFlexVar vty gl' spine ->
          if gl == gl'
          then throwError OccursCheck
          else do
            tty <- go pren vty
            goSpine pren (C.Meta gl' tty) spine
        N.StuckRigidVar vty lv spine -> case Map.lookup lv (ren pren) of
          Just lv' -> do
            tty <- go pren vty
            goSpine pren (C.Var (N.lvToIx (domain pren) lv') tty) spine
          Nothing -> throwError EscapingVar
        N.FunIntro body vty@(N.FunType inTy _) -> do
          tty <- go pren vty
          vBody <- lift $ runNorm (domain pren) $ N.appClosure body (N.StuckRigidVar inTy (codomain pren) [])
          bodyTrm <- go (inc pren) vBody
          liftEither $ Right $ C.FunIntro bodyTrm tty
        N.FunType inTy outTy -> do
          inTyTrm <- go pren inTy
          vOutTy <- lift $ runNorm (domain pren) $ N.appClosure outTy (N.StuckRigidVar inTy (codomain pren) [])
          outTyTrm <- go (inc pren) vOutTy
          liftEither $ Right $ C.FunType inTyTrm outTyTrm
        N.StagedType innerTy stage -> do
          innerTyTrm <- go pren innerTy
          liftEither $ Right $ C.StagedType innerTyTrm stage
        N.StuckStagedIntro inner innerTy stage spine -> do
          innerTrm <- goTerm (inc pren) inner
          innerTyTrm <- go (inc pren) innerTy
          goSpine pren (C.StagedIntro innerTrm innerTyTrm stage) spine
        N.StuckStagedElim scr ty body stage spine -> do
          scrTrm <- go pren scr
          tyTrm <- go pren ty
          bodyTrm <- go (inc pren) body
          goSpine pren (C.StagedElim scrTrm tyTrm bodyTrm stage) spine
        N.TypeType -> liftEither $ Right C.TypeType
        N.ElabError -> liftEither $ Right C.ElabError

getTtySpine :: N.Metas -> Level -> N.Type -> N.Spine -> C.Term
getTtySpine metas lv vty spine = case (vty, spine) of
  (N.FunType inTy outTy, _:spine) -> getTtySpine
    metas
    (incLevel lv)
    (runReader (N.appClosure outTy (N.StuckRigidVar inTy lv [])) (lv, metas, Set.singleton C.T, []))
    spine
  (_, []) -> runReader (N.readback vty) (lv, metas, Set.singleton C.T, [])

getTty :: N.Metas -> Level -> N.Value -> C.Term
getTty metas lv val = case val of
  N.StuckFlexVar vty _ spine -> getTtySpine metas lv vty spine
  N.StuckRigidVar vty _ spine -> getTtySpine metas lv vty spine
  N.FunIntro _ vty -> runReader (N.readback vty) (lv, metas, Set.singleton C.T, [])
  N.FunType _ _ -> C.TypeType
  N.TypeType -> C.TypeType

getVtySpine :: N.Metas -> Level -> N.Type -> N.Spine -> N.Value
getVtySpine metas lv vty spine = case (vty, spine) of
  (N.FunType inTy outTy, _:spine) -> getVtySpine
    metas
    (incLevel lv)
    (runReader (N.appClosure outTy (N.StuckRigidVar inTy lv [])) (lv, metas, Set.singleton C.T, []))
    spine
  (_, []) -> vty

getVty :: N.Metas -> Level -> N.Value -> N.Value
getVty metas lv val = case val of
  N.StuckFlexVar vty _ spine -> getVtySpine metas lv vty spine
  N.StuckRigidVar vty _ spine -> getVtySpine metas lv vty spine
  N.FunIntro _ vty -> vty
  N.FunType _ _ -> N.TypeType
  N.TypeType -> N.TypeType

lams :: Level -> [C.Term] -> C.Term -> C.Term
lams lv ttys trm = go (Level 0) ttys
  where
    go lv' ttys =
        if lv == lv'
        then trm
        else
          let (tty, ttys) = fromJust $ uncons ttys
          in C.FunIntro (go (Level $ unLevel lv' + 1) ttys) tty

solve :: Level -> Global -> N.Spine -> N.Value -> Unify ()
solve gamma gl spine rhs = do
  metas <- getMetas
  pren <- runExceptT $ invert metas gamma spine
  case pren of
    Right pren -> do
      rhs <- runExceptT $ rename metas gl pren rhs
      case rhs of
        Right rhs -> do
          solution <- runNorm gamma $ N.eval (lams (domain pren) (map (getTty metas (domain pren)) spine) rhs)
          putSolution gl solution
        Left err -> putError err
    Left err -> putError err

unifySpines :: Level -> N.Spine -> N.Spine -> Unify ()
unifySpines lv spine spine'= case (spine, spine') of
  (arg:spine, arg':spine') -> do
    unifySpines lv spine spine'
    unify lv arg arg'
  ([], []) -> pure ()
  _ -> putError InvalidSpine

unifyStages :: C.Stage -> C.Stage -> Unify ()
unifyStages s s' = case (s, s') of
  (C.StageMeta gl, C.StageMeta gl') | gl == gl' -> pure ()
  (C.StageMeta gl, s') -> putStageSolution gl s'
  (s, C.StageMeta gl) -> putStageSolution gl s
  (s, s') | s == s' -> pure ()
  _ -> putError $ MismatchStages s s'

unifyTerms :: Level -> C.Term -> C.Term -> Unify ()
unifyTerms lv trm trm' = undefined

unify :: Level -> N.Value -> N.Value -> Unify ()
unify lv val val' = do
  val <- runNorm lv $ N.force val
  val' <- runNorm lv $ N.force val'
  metasForGetVty <- getMetas
  case (val, val') of
    (N.FunIntro body vty@(N.FunType inTy _), N.FunIntro body' vty'@(N.FunType inTy' _)) -> do
      unify lv vty vty'
      vBody <- runNorm (incLevel lv) $ N.appClosure body (N.StuckRigidVar inTy lv [])
      vBody' <- runNorm (incLevel lv) $ N.appClosure body' (N.StuckRigidVar inTy' lv [])
      unify (incLevel lv) vBody vBody'
    (val, N.FunIntro body vty@(N.FunType inTy' _)) | valTy@(N.FunType inTy _) <- getVty metasForGetVty lv val -> do
      unify lv valTy vty
      vAppVal <- runNorm lv $ N.vApp val (N.StuckRigidVar inTy lv [])
      vBody <- runNorm (incLevel lv) $ N.appClosure body (N.StuckRigidVar inTy' lv [])
      unify (incLevel lv) vAppVal vBody
    (N.FunIntro body vty@(N.FunType inTy _), val') | valTy@(N.FunType inTy' _) <- getVty metasForGetVty lv val' -> do
      unify lv valTy vty
      vBody <- runNorm (incLevel lv) $ N.appClosure body (N.StuckRigidVar inTy lv [])
      vAppVal <- runNorm lv $ N.vApp val (N.StuckRigidVar inTy' lv [])
      unify (incLevel lv) vBody vAppVal
    (N.StagedType innerTy stage, N.StagedType innerTy' stage') -> do
      unifyStages stage stage'
      unify (incLevel lv) innerTy innerTy'
    (N.StuckStagedIntro inner innerTy stage spine, N.StuckStagedIntro inner' innerTy' stage' spine') -> do
      unifyStages stage stage'
      unify (incLevel lv) innerTy innerTy'
      unifyTerms (incLevel lv) inner inner'
      unifySpines lv spine spine'
    (N.StuckStagedElim scr ty body stage spine, N.StuckStagedElim scr' ty' body' stage' spine') -> do
      unifyStages stage stage'
      unify lv ty ty'
      unify lv scr scr'
      unify (incLevel lv) body body'
      unifySpines lv spine spine'
    (N.TypeType, N.TypeType) -> pure ()
    (N.FunType inTy outTy, N.FunType inTy' outTy') -> do
      unify lv inTy inTy'
      vOutTy <- runNorm (incLevel lv) $ N.appClosure outTy (N.StuckRigidVar inTy lv [])
      vOutTy' <- runNorm (incLevel lv) $ N.appClosure outTy' (N.StuckRigidVar inTy' lv [])
      unify (incLevel lv) vOutTy vOutTy'
    (N.StuckRigidVar vty rlv spine, N.StuckRigidVar vty' rlv' spine') | rlv == rlv' -> do
      unify lv vty vty'
      unifySpines lv spine spine'
    (N.StuckFlexVar vty gl spine, N.StuckFlexVar vty' gl' spine') | gl == gl' -> do
      unify lv vty vty'
      unifySpines lv spine spine
    -- FIXME? Unify types
    (val, N.StuckFlexVar _ gl spine) -> solve lv gl spine val
    (N.StuckFlexVar _ gl spine, val') -> solve lv gl spine val'
    (N.ElabError, _) -> pure ()
    (_, N.ElabError) -> pure ()
    _ -> putError $ Mismatch val val'