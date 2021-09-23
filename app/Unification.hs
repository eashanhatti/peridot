{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
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
import GHC.Stack
import Debug.Trace

data Error
  = InvalidSpine
  | OccursCheck
  | EscapingVar
  | Mismatch N.Value N.Value
  | MismatchSpines N.Spine N.Spine

instance Show Error where
  show e = case e of
    InvalidSpine -> "Invalid Spine "
    OccursCheck -> "Failed Occurs Check"
    EscapingVar -> "Escaping Var"
    Mismatch val val' -> "Mismatched Types:\n  " ++ show val ++ "\n  " ++ show val'

newtype Unify a = Unify (State (N.Metas, [Error]) a)

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

get :: Unify (N.Metas, [Error])
get = Unify $ state $ \s -> (s, s)

put :: (N.Metas, [Error]) -> Unify ()
put s = Unify $ state $ \_ -> ((), s)

runUnify :: Unify a -> (N.Metas, [Error]) -> (a, (N.Metas, [Error]))
runUnify (Unify act) s = runState act s

runNorm :: Level -> N.Norm a -> Unify a
runNorm lv act = do
  (metas, _) <- get
  pure $ runReader act (lv, metas, [])

putSolution :: Global -> N.Value -> Unify ()
putSolution gl sol = do
  (metas, errors) <- get
  put (Map.insert gl (N.Solved sol) metas, errors)

putError :: Error -> Unify ()
putError err = do
  (metas, errors) <- get
  put (metas, err:errors)

getMetas :: Unify N.Metas
getMetas = do
  (metas, _) <- get
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
invert metas gamma spine' = do
  let go :: N.Spine -> ExceptT Error Unify (Level, Map.Map Level Level)
      go = \case
        (arg:spine) -> do
          (domain, ren) <- go spine
          arg <- lift $ runNorm gamma $ N.force arg
          -- let !() = trace ("    Renaming = " ++ show ren ++ "  Arg = " ++ show arg ++ "  Spine = " ++ show spine') ()
          case arg of
            N.StuckRigidVar _ lv [] | Map.notMember lv ren -> liftEither $ Right (Level $ unLevel domain + 1, Map.insert lv domain ren)
            _ -> throwError InvalidSpine
        [] -> liftEither $ Right (Level 0, mempty)
  (domain, ren) <- go spine'
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
        N.TypeType0 -> liftEither $ Right C.TypeType0
        N.TypeType1 -> liftEither $ Right C.TypeType1
        N.ElabError -> liftEither $ Right C.ElabError

getTtySpine :: N.Metas -> Level -> N.Type -> N.Spine -> C.Term
getTtySpine metas lv vty spine = case (vty, spine) of
  (N.FunType inTy outTy, _:spine) -> getTtySpine
    metas
    (incLevel lv)
    (runReader (N.appClosure outTy (N.StuckRigidVar inTy lv [])) (lv, metas, []))
    spine
  (_, []) -> runReader (N.readback vty) (lv, metas, [])

getTty :: N.Metas -> Level -> N.Value -> C.Term
getTty metas lv val = case val of
  N.StuckFlexVar vty _ spine -> getTtySpine metas lv vty spine
  N.StuckRigidVar vty _ spine -> getTtySpine metas lv vty spine
  N.FunIntro _ vty -> runReader (N.readback vty) (lv, metas, [])
  N.FunType inTy _ -> getTty metas lv inTy -- NOTE: this assumes that inTy and outTy are of the same universe
  N.TypeType0 -> C.TypeType0
  N.TypeType1 -> C.TypeType1

getVtySpine :: N.Metas -> Level -> N.Type -> N.Spine -> N.Value
getVtySpine metas lv vty spine = case (vty, spine) of
  (N.FunType inTy outTy, _:spine) -> getVtySpine
    metas
    (incLevel lv)
    (runReader (N.appClosure outTy (N.StuckRigidVar inTy lv [])) (lv, metas, []))
    spine
  (_, []) -> vty

getVty :: N.Metas -> Level -> N.Value -> N.Value
getVty metas lv val = case val of
  N.StuckFlexVar vty _ spine -> getVtySpine metas lv vty spine
  N.StuckRigidVar vty _ spine -> getVtySpine metas lv vty spine
  N.FunIntro _ vty -> vty
  N.FunType inTy _ -> getVty metas lv inTy
  N.TypeType0 -> N.TypeType0
  N.TypeType1 -> N.TypeType1

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
  _ -> putError $ MismatchSpines spine spine'

unify :: HasCallStack => Level -> N.Value -> N.Value -> Unify ()
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
    (N.TypeType0, N.TypeType0) -> pure ()
    (N.TypeType1, N.TypeType1) -> pure ()
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