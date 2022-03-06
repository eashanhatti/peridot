module Codegen.Lower where

import Syntax.Object qualified as O
import Syntax.STG qualified as L
import Syntax.Extra
import Data.Map qualified as Map
import Data.Set qualified as Set
import Control.Effect.State
import Control.Algebra(Has)
import Control.Monad

data LowerState = LowerState
  { unReps :: Map.Map Id RuntimeRep
  , unDecls :: [([L.Declaration], [(L.Binding, L.Term)])] }

type Lower sig m = Has (State LowerState) sig m

lower :: Lower sig m => O.Term -> m L.Term
lower (O.FunType inTy outTy) = L.Val <$> (L.Arrow <$> lowerBind inTy <*> lowerBind outTy)
lower (funIntro -> (tys@(null -> False), body)) = do
  name <- freshId
  bs <- traverse (\ty -> L.Binding <$> repOf ty <*> freshId) tys
  lBody <- lower body
  vs <- freeVars lBody
  L.Val <$> bindDecl (L.Fun name vs bs lBody)
lower (con -> Just (did, args)) = L.Val <$> (L.Con did <$> traverse lowerBind args)
lower (funElim -> (lam, args@(null -> False))) =
  L.App <$> lowerBind lam <*> traverse lowerBind args
lower (O.IOType ty) = L.Val <$> (L.IOType <$> lowerBind ty)
lower (O.IOIntro1 term) = lower term
lower (O.IOIntro2 act k) = L.DoIO act <$> lower k
lower O.UnitIntro = pure (L.Val L.Unit)
lower O.UnitType = pure (L.Val L.UnitType)
lower (O.TypeType (Object rep)) = pure (L.Val (L.Univ rep))
lower (O.LocalVar ix) = L.Val <$> localVar ix
lower (O.GlobalVar did) = L.Val <$> globalVar did
lower (O.Let decls body) = do
  addDecls decls
  L.Letrec <$> filterMapM lowerDecl decls <*> lower body

lowerBind :: Lower sig m => O.Term -> m L.Value
lowerBind = lower >=> bindTerm

con :: O.Term -> Maybe (Id, [O.Term])
con (O.FunElim lam arg) = do
  (did, args) <- con lam
  pure (did, args ++ [arg])
con (O.ObjectConstantIntro did) = pure (did, [])
con _ = Nothing

funElim :: O.Term -> (O.Term, [O.Term])
funElim (O.FunElim lam arg) =
  let (lam', args) = funElim lam
  in (lam', args ++ [arg])

funIntro :: O.Term -> ([O.Type], O.Term)
funIntro (O.FunIntro ty body) =
  let (tys, body') = funIntro body
  in (ty:tys, body')

lowerDecl :: Lower sig m => O.Declaration -> m (Maybe L.Declaration)
lowerDecl (O.Term _ sig def@(O.FunIntro _ _)) = Just <$> funDecl [] def
lowerDecl (O.Term _ _ def) = do
  name <- freshId
  lDef <- lower def
  pure (Just (L.Thunk name lDef))
lowerDecl (O.ObjectConstant _ _) = pure Nothing

funDecl :: Lower sig m => [L.Binding] -> O.Term -> m L.Declaration
funDecl bs body = do
  name <- freshId
  lBody <- lower body
  vs <- freeVars lBody
  pure (L.Fun name vs bs lBody)
funDecl bs (O.FunIntro ty body) = do
  name <- freshId
  rep <- repOf ty
  funDecl (bs ++ [L.Binding rep name]) body

addDecls :: Lower sig m => [O.Declaration] -> m ()
addDecls [] = pure ()
addDecls ((O.unSig -> sig) : decls) = do
  rep <- repOf sig
  name <- freshId
  state <- get
  put (state { unReps = Map.insert name rep (unReps state) })
  addDecls decls

repOf :: Lower sig m => O.Signature -> m RuntimeRep
repOf = undefined

filterMapM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
filterMapM f [] = pure []
filterMapM f (x:xs) = do
  mx <- f x
  case mx of
    Just mx -> (mx :) <$> filterMapM f xs
    Nothing -> filterMapM f xs

freshId :: Lower sig m => m Id
freshId = undefined

freeVars :: Lower sig m => L.Term -> m (Set.Set Id)
freeVars = undefined

bindTerm :: Lower sig m => L.Term -> m L.Value
bindTerm = undefined

bindDecl :: Lower sig m => L.Declaration -> m L.Value
bindDecl = undefined

localVar :: Lower sig m => Index -> m L.Value
localVar = undefined

globalVar :: Lower sig m => Id -> m L.Value
globalVar = undefined
