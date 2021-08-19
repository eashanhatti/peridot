{-# LANGUAGE LambdaCase #-}

module Unification where

import qualified Data.Map as Map
import qualified Eval as E
import qualified Core as C
import Var
import Data.List(uncons)
import Data.Maybe(fromJust)
import Control.Monad.State(State, get, put)

-- FIXME
data Error = InvalidSpine | OccursCheck | EscapingVar | Mismatch
  deriving Show

type Unify a = State (E.Metas, [Error]) a

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
  pure $ E.force metas val

getMetas :: Unify E.Metas
getMetas = do
  (metas, _) <- get
  pure metas

data PartialRenaming = PartialRenaming
  { domain :: Level
  , codomain :: Level
  , ren :: Map.Map Level Level }

lift :: PartialRenaming -> PartialRenaming
lift pren = PartialRenaming
  (Level $ unLevel (domain pren) + 1)
  (Level $ unLevel (codomain pren) + 1)
  (Map.insert (codomain pren) (domain pren) (ren pren))

invert :: E.Metas -> Level -> E.Spine -> Either Error PartialRenaming
invert metas gamma spine = do
  let go :: E.Spine -> Either Error (Level, Map.Map Level Level)
      go = \case
        (arg:spine) -> do
          (domain, ren) <- go spine
          case E.force metas arg of
            E.StuckRigidVar _ lv [] | Map.notMember lv ren -> Right (Level $ unLevel domain + 1, Map.insert lv domain ren)
            _ -> Left InvalidSpine
        [] -> Right (Level 0, mempty)
  (domain, ren) <- go spine
  Right $ PartialRenaming domain gamma ren

rename :: E.Metas -> Global -> PartialRenaming -> E.Value -> Either Error C.Term
rename metas gl pren rhs = go pren rhs
  where
    goSpine :: PartialRenaming -> C.Term -> E.Spine -> Either Error C.Term
    goSpine pren val spine = case spine of
      (arg:spine) -> C.FunElim <$> goSpine pren val spine <*> go pren arg
      [] -> Right val

    go :: PartialRenaming -> E.Value -> Either Error C.Term
    go pren val = case E.force metas val of
      E.StuckFlexVar vty gl' spine ->
        if gl == gl'
        then Left OccursCheck
        else do
          tty <- go pren vty
          goSpine pren (C.Meta gl' tty) spine
      E.StuckRigidVar vty lv spine -> case Map.lookup lv (ren pren) of
        Just lv' -> do
          tty <- go pren vty
          goSpine pren (C.Var (E.lvToIx (domain pren) lv') tty) spine
        Nothing -> Left EscapingVar
      E.FunIntro body vty@(E.FunType inTy _) -> do
        tty <- go pren vty
        bodyTrm <- go (lift pren) (E.appClosure metas body (E.StuckRigidVar inTy (codomain pren) []))
        Right $ C.FunIntro bodyTrm tty
      E.FunType inTy outTy -> do
        inTyTrm <- go pren inTy
        outTyTrm <- go (lift pren) (E.appClosure metas outTy (E.StuckRigidVar inTy (codomain pren) []))
        Right $ C.FunType inTyTrm outTyTrm
      E.TypeType -> Right C.TypeType

getTtySpine :: E.Metas -> Level -> E.Type -> E.Spine -> C.Term
getTtySpine metas lv vty spine = case (vty, spine) of
  (E.FunType inTy outTy, _:spine) -> getTtySpine metas (incLevel lv) (E.appClosure metas outTy (E.StuckRigidVar inTy lv [])) spine
  (_, []) -> E.readback metas lv vty

getTty :: E.Metas -> Level -> E.Value -> C.Term
getTty metas lv val = case val of
  E.StuckFlexVar vty _ spine -> getTtySpine metas lv vty spine
  E.StuckRigidVar vty _ spine -> getTtySpine metas lv vty spine
  E.FunIntro _ vty -> E.readback metas lv vty
  E.FunType _ _ -> C.TypeType
  E.TypeType -> C.TypeType

getVtySpine :: E.Metas -> Level -> E.Type -> E.Spine -> E.Value
getVtySpine metas lv vty spine = case (vty, spine) of
  (E.FunType inTy outTy, _:spine) -> getVtySpine metas (incLevel lv) (E.appClosure metas outTy (E.StuckRigidVar inTy lv [])) spine
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
solve gamma gl spine rhs= do
  metas <- getMetas
  case invert metas gamma spine of
    Right pren ->
      case rename metas gl pren rhs of
        Right rhs -> do
          let solution = E.eval metas [] (lams (domain pren) (map (getTty metas (domain pren)) spine) rhs)
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
      metas <- getMetas
      unify (incLevel lv) (E.appClosure metas body (E.StuckRigidVar inTy lv [])) (E.appClosure metas body' (E.StuckRigidVar inTy' lv []))
    (val, E.FunIntro body vty@(E.FunType inTy' _)) | valTy@(E.FunType inTy _) <- getVty metasForGetVty lv val -> do
      unify lv valTy vty
      metas <- getMetas
      unify (incLevel lv) (E.vApp metas val (E.StuckRigidVar inTy lv [])) (E.appClosure metas body (E.StuckRigidVar inTy' lv []))
    (E.FunIntro body vty@(E.FunType inTy _), val') | valTy@(E.FunType inTy' _) <- getVty metasForGetVty lv val' -> do
      unify lv valTy vty
      metas <- getMetas
      unify (incLevel lv) (E.appClosure metas body (E.StuckRigidVar inTy lv [])) (E.vApp metas val (E.StuckRigidVar inTy' lv []))
    (E.TypeType, E.TypeType) -> pure ()
    (E.FunType inTy outTy, E.FunType inTy' outTy') -> do
      unify lv inTy inTy'
      metas <- getMetas
      unify (incLevel lv) (E.appClosure metas outTy (E.StuckRigidVar inTy lv [])) (E.appClosure metas outTy' (E.StuckRigidVar inTy' lv []))
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
    _ -> putError Mismatch