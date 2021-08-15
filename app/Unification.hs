module Unification where

import qualified Data.Map as Map
import qualified Eval as E
import qualified Core as C
import Var

-- FIXME
data UnifyError = InvalidSpine | OccursCheck | EscapingVar | Mismatch

type Unify a = Either UnifyError a

data PartialRenaming = PartialRenaming
  { domain :: Level
  , codomain :: Level
  , ren :: Map.Map Level Level }

lift :: PartialRenaming -> PartialRenaming
lift pren = undefined

invert :: E.Metas -> Level -> E.Spine -> Unify PartialRenaming
invert metas gamma spine = do
  let go :: E.Spine -> Unify (Level, Map.Map Level Level)
      go = \case
        (arg:spine) -> do
          (domain, ren) <- go spine
          case E.force metas arg of
            E.StuckRigidVar _ lv [] | Map.notMember lv ren -> Right (Level $ unLevel domain + 1, Map.insert lv domain ren)
            _ -> Left InvalidSpine
        [] -> Right (Level 0, mempty)
  (domain, ren) <- go spine
  Right $ PartialRenaming domain gamma ren

rename :: E.Metas -> Global -> PartialRenaming -> E.Value -> Unify C.Term
rename metas gl pren rhs = go pren rhs
  where
    goSpine :: PartialRenaming -> C.Term -> E.Spine -> Unify C.Term
    goSpine pren val spine = case spine of
      (arg:spine) -> C.FunElim <$> goSpine pren val spine <*> go pren arg
      [] -> Right val

    go :: PartialRenaming -> E.Value -> Unify C.Term
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
    go lv' (tty:ttys) =
      if lv == lv'
      then trm
      else C.FunIntro (go (Level $ unLevel lv' + 1) ttys) tty  

solve :: E.Metas -> Level -> Global -> E.Spine -> E.Value -> Unify E.Value
solve metas gamma gl spine rhs = do
  pren <- invert metas gamma spine
  rhs <- rename metas gl pren rhs
  Right $ E.eval metas [] (lams (domain pren) (map (getTty metas (domain pren)) spine) rhs)

unifySpines :: E.Metas -> Level -> E.Spine -> E.Spine -> Unify E.Metas
unifySpines = undefined

unify :: E.Metas -> Level -> E.Value -> E.Value -> Unify E.Metas
unify metas lv val val' = case (E.force metas val, E.force metas val') of
  (E.FunIntro body vty@(E.FunType inTy _), E.FunIntro body' vty'@(E.FunType inTy' _)) -> do
    metas <- unify metas lv vty vty'
    unify metas (incLevel lv) (E.appClosure metas body (E.StuckRigidVar inTy lv [])) (E.appClosure metas body' (E.StuckRigidVar inTy' lv []))
  (val, E.FunIntro body vty@(E.FunType inTy' _)) | valTy@(E.FunType inTy _) <- getVty metas lv val -> do
    metas <- unify metas lv valTy vty
    unify metas (incLevel lv) (E.vApp metas val (E.StuckRigidVar inTy lv [])) (E.appClosure metas body (E.StuckRigidVar inTy' lv []))
  (E.FunIntro body vty@(E.FunType inTy _), val') | valTy@(E.FunType inTy' _) <- getVty metas lv val' -> do
    metas <- unify metas lv valTy vty
    unify metas (incLevel lv) (E.appClosure metas body (E.StuckRigidVar inTy lv [])) (E.vApp metas val (E.StuckRigidVar inTy' lv []))
  (E.TypeType, E.TypeType) -> Right metas
  (E.FunType inTy outTy, E.FunType inTy' outTy') -> do
    metas <- unify metas lv inTy inTy'
    unify metas (incLevel lv) (E.appClosure metas outTy (E.StuckRigidVar inTy lv [])) (E.appClosure metas outTy' (E.StuckRigidVar inTy' lv []))
  (E.StuckRigidVar vty rlv spine, E.StuckRigidVar vty' rlv' spine') | rlv == rlv' -> do
    metas <- unify metas lv vty vty'
    unifySpines metas lv spine spine'
  (E.StuckFlexVar vty gl spine, E.StuckFlexVar vty' gl' spine') | gl == gl' -> do
    metas <- unify metas lv vty vty'
    unifySpines metas lv spine spine'
  -- FIXME? Unify types
  (val, E.StuckFlexVar _ gl spine) -> do
    solution <- solve metas lv gl spine val
    Right $ Map.insert gl (E.Solved solution) metas
  (E.StuckFlexVar _ gl spine, val') -> do
    solution <- solve metas lv gl spine val'
    Right $ Map.insert gl (E.Solved solution) metas
  _ -> Left Mismatch