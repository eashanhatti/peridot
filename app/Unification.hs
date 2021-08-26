{-# LANGUAGE LambdaCase #-}
-- {-# OPTIONS_GHC -fdefer-type-errors #-}

module Unification where

import qualified Data.Map as Map
import qualified Eval as E
import qualified Core as C
import Var
import Data.List(uncons)
import Data.Maybe(fromJust)
import Data.Functor.Identity(Identity)
import Control.Monad.State(State, state, runState)
import Control.Monad.Reader(runReader)
import Control.Monad.Except(ExceptT, lift, throwError, liftEither, runExceptT)
import Control.Monad(ap, liftM)

-- FIXME
data Error = InvalidSpine | OccursCheck | EscapingVar | Mismatch E.Value E.Value
  deriving Show

newtype Unify a = Unify { runUnify :: State (E.Metas, [Error]) a }

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

get :: Unify (E.Metas, [Error])
get = Unify $ state $ \s -> (s, s)

put :: (E.Metas, [Error]) -> Unify ()
put s = Unify $ state $ \_ -> ((), s)

runNorm :: E.Norm a -> Unify a
runNorm act = do
  (metas, _) <- get
  pure $ runReader act (metas, C.T, [])

putSolution :: Global -> E.Value -> Unify ()
putSolution gl sol = do
  (metas, probs) <- get
  put (Map.insert gl (E.Solved sol) metas, probs)

putError :: Error -> Unify ()
putError err = do
  (metas, errors) <- get
  put (metas, err:errors)

force :: E.Value -> Unify E.Value
force val = do
  (metas, _) <- get
  runNorm $ E.force val

getMetas :: Unify E.Metas
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

invert :: E.Metas -> Level -> E.Spine -> ExceptT Error Unify PartialRenaming
invert metas gamma spine = do
  let go :: E.Spine -> ExceptT Error Unify (Level, Map.Map Level Level)
      go = \case
        (arg:spine) -> do
          (domain, ren) <- go spine
          arg <- lift $ runNorm $ E.force arg
          case arg of
            E.StuckRigidVar _ lv [] | Map.notMember lv ren -> liftEither $ Right (Level $ unLevel domain + 1, Map.insert lv domain ren)
            _ -> throwError InvalidSpine
        [] -> liftEither $ Right (Level 0, mempty)
  (domain, ren) <- go spine
  liftEither $ Right $ PartialRenaming domain gamma ren

rename :: E.Metas -> Global -> PartialRenaming -> E.Value -> ExceptT Error Unify C.Term
rename metas gl pren rhs = go pren rhs
  where
    goSpine :: PartialRenaming -> C.Term -> E.Spine -> ExceptT Error Unify C.Term
    goSpine pren val spine = case spine of
      (arg:spine) -> C.FunElim <$> goSpine pren val spine <*> go pren arg
      [] -> liftEither $ Right val

    go :: PartialRenaming -> E.Value -> ExceptT Error Unify C.Term
    go pren val = do
      val <- lift $ runNorm $ E.force val
      case val of
        E.StuckFlexVar vty gl' spine ->
          if gl == gl'
          then throwError OccursCheck
          else do
            tty <- go pren vty
            goSpine pren (C.Meta gl' tty) spine
        E.StuckRigidVar vty lv spine -> case Map.lookup lv (ren pren) of
          Just lv' -> do
            tty <- go pren vty
            goSpine pren (C.Var (E.lvToIx (domain pren) lv') tty) spine
          Nothing -> throwError EscapingVar
        E.FunIntro body vty@(E.FunType inTy _) -> do
          tty <- go pren vty
          vBody <- lift $ runNorm $ E.appClosure body (E.StuckRigidVar inTy (codomain pren) [])
          bodyTrm <- go (inc pren) vBody
          liftEither $ Right $ C.FunIntro bodyTrm tty
        E.FunType inTy outTy -> do
          inTyTrm <- go pren inTy
          vOutTy <- lift $ runNorm $ E.appClosure outTy (E.StuckRigidVar inTy (codomain pren) [])
          outTyTrm <- go (inc pren) vOutTy
          liftEither $ Right $ C.FunType inTyTrm outTyTrm
        E.TypeType -> liftEither $ Right C.TypeType
        E.ElabError -> liftEither $ Right C.ElabError

getTtySpine :: E.Metas -> Level -> E.Type -> E.Spine -> C.Term
getTtySpine metas lv vty spine = case (vty, spine) of
  (E.FunType inTy outTy, _:spine) -> getTtySpine
    metas
    (incLevel lv)
    (runReader (E.appClosure outTy (E.StuckRigidVar inTy lv [])) (metas, C.T, []))
    spine
  (_, []) -> runReader (E.readback lv vty) (metas, C.T, [])

getTty :: E.Metas -> Level -> E.Value -> C.Term
getTty metas lv val = case val of
  E.StuckFlexVar vty _ spine -> getTtySpine metas lv vty spine
  E.StuckRigidVar vty _ spine -> getTtySpine metas lv vty spine
  E.FunIntro _ vty -> runReader (E.readback lv vty) (metas, C.T, [])
  E.FunType _ _ -> C.TypeType
  E.TypeType -> C.TypeType

getVtySpine :: E.Metas -> Level -> E.Type -> E.Spine -> E.Value
getVtySpine metas lv vty spine = case (vty, spine) of
  (E.FunType inTy outTy, _:spine) -> getVtySpine
    metas
    (incLevel lv)
    (runReader (E.appClosure outTy (E.StuckRigidVar inTy lv [])) (metas, C.T, []))
    spine
  (_, []) -> vty

getVty :: E.Metas -> Level -> E.Value -> E.Value
getVty metas lv val = case val of
  E.StuckFlexVar vty _ spine -> getVtySpine metas lv vty spine
  E.StuckRigidVar vty _ spine -> getVtySpine metas lv vty spine
  E.FunIntro _ vty -> vty
  E.FunType _ _ -> E.TypeType
  E.TypeType -> E.TypeType

lams :: Level -> [C.Term] -> C.Term -> C.Term
lams lv ttys trm = go (Level 0) ttys
  where
    go lv' ttys =
        if lv == lv'
        then trm
        else
          let (tty, ttys) = fromJust $ uncons ttys
          in C.FunIntro (go (Level $ unLevel lv' + 1) ttys) tty

solve :: Level -> Global -> E.Spine -> E.Value -> Unify ()
solve gamma gl spine rhs = do
  metas <- getMetas
  pren <- runExceptT $ invert metas gamma spine
  case pren of
    Right pren -> do
      rhs <- runExceptT $ rename metas gl pren rhs
      case rhs of
        Right rhs -> do
          solution <- runNorm $ E.eval (lams (domain pren) (map (getTty metas (domain pren)) spine) rhs)
          putSolution gl solution
        Left err -> putError err
    Left err -> putError err

unifySpines :: Level -> E.Spine -> E.Spine-> Unify ()
unifySpines lv spine spine'= case (spine, spine') of
  (arg:spine, arg':spine') -> do
    unifySpines lv spine spine'
    unify lv arg arg'
  ([], []) -> pure ()
  _ -> putError InvalidSpine

unify :: Level -> E.Value -> E.Value -> Unify ()
unify lv val val' = do
  val <- force val
  val' <- force val'
  metasForGetVty <- getMetas
  case (val, val') of
    (E.FunIntro body vty@(E.FunType inTy _), E.FunIntro body' vty'@(E.FunType inTy' _)) -> do
      unify lv vty vty'
      vBody <- runNorm $ E.appClosure body (E.StuckRigidVar inTy lv [])
      vBody' <- runNorm $ E.appClosure body' (E.StuckRigidVar inTy' lv [])
      unify (incLevel lv) vBody vBody'
    (val, E.FunIntro body vty@(E.FunType inTy' _)) | valTy@(E.FunType inTy _) <- getVty metasForGetVty lv val -> do
      unify lv valTy vty
      vAppVal <- runNorm $ E.vApp val (E.StuckRigidVar inTy lv [])
      vBody <- runNorm $ E.appClosure body (E.StuckRigidVar inTy' lv [])
      unify (incLevel lv) vAppVal vBody
    (E.FunIntro body vty@(E.FunType inTy _), val') | valTy@(E.FunType inTy' _) <- getVty metasForGetVty lv val' -> do
      unify lv valTy vty
      vBody <- runNorm $ E.appClosure body (E.StuckRigidVar inTy lv [])
      vAppVal <- runNorm $ E.vApp val (E.StuckRigidVar inTy' lv [])
      unify (incLevel lv) vBody vAppVal
    (E.TypeType, E.TypeType) -> pure ()
    (E.FunType inTy outTy, E.FunType inTy' outTy') -> do
      unify lv inTy inTy'
      vOutTy <- runNorm $ E.appClosure outTy (E.StuckRigidVar inTy lv [])
      vOutTy' <- runNorm $ E.appClosure outTy' (E.StuckRigidVar inTy' lv [])
      unify (incLevel lv) vOutTy vOutTy'
    (E.StuckRigidVar vty rlv spine, E.StuckRigidVar vty' rlv' spine') | rlv == rlv' -> do
      unify lv vty vty'
      unifySpines lv spine spine'
    (E.StuckFlexVar vty gl spine, E.StuckFlexVar vty' gl' spine') | gl == gl' -> do
      unify lv vty vty'
      unifySpines lv spine spine
    -- FIXME? Unify types
    (val, E.StuckFlexVar _ gl spine) -> solve lv gl spine val
    (E.StuckFlexVar _ gl spine, val') -> solve lv gl spine val'
    (E.ElabError, _) -> pure ()
    (_, E.ElabError) -> pure ()
    _ -> putError $ Mismatch val val'