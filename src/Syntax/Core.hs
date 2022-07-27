module Syntax.Core
( module Syntax.Core
, module Syntax.Common
) where

import Syntax.Common hiding(unId, Declaration)
import Syntax.Common qualified as Cm
import Data.Map
import Data.Sequence
import Numeric.Natural

type Type = Term

data Term
  -- Object level
  = ObjFunType PassMethod Term Term
  | ObjFunIntro Term
  | ObjFunElim Term Term
  | TwoElim Term Term Term
  | RecType (Seq (Field, Term))
  | RecIntro (Seq (Field, Term))
  | RecElim Term Field
  | SingElim Term
  -- Meta level
  | MetaFunType PassMethod Term Term
  | MetaFunIntro Term
  | MetaFunElim Term Term
  | CodeObjElim Term
  | CodeCElim Term
  | TextElimCat Term Term
  -- Other
  | LocalVar Index
  | GlobalVar Term Bool
  | UniVar Global (Maybe Term)
  | Rigid (RigidTerm Term)
  | Declare Universe Term Term Term -- univ, name, ty, cont
  | Define Term Term Term -- name, def, cont
  deriving (Eq, Show)

pattern ObjTypeType = Rigid (TypeType Obj)
pattern MetaTypeType = Rigid (TypeType Meta)

viewObjFunTys :: Term -> (Seq (PassMethod, Term), Term)
viewObjFunTys (ObjFunType pm inTy outTy) =
  let (inTys, outTy') = viewObjFunTys outTy
  in ((pm, inTy) <| inTys, outTy')
viewObjFunTys e = (mempty, e)

viewMetaFunTys :: Term -> (Seq (PassMethod, Term), Term)
viewMetaFunTys (MetaFunType pm inTy outTy) =
  let (inTys, outTy') = viewMetaFunTys outTy
  in ((pm, inTy) <| inTys, outTy')
viewMetaFunTys e = (mempty, e)

viewObjFunIntros :: Term -> (Natural, Term)
viewObjFunIntros (ObjFunIntro body) =
  let (n, body') = viewObjFunIntros body
  in (n + 1, body')
viewObjFunIntros e = (0, e)

viewMetaFunIntros :: Term -> (Natural, Term)
viewMetaFunIntros (MetaFunIntro body) =
  let (n, body') = viewObjFunIntros body
  in (n + 1, body')
viewMetaFunIntros e = (0, e)

viewFunElims :: Term -> (Term, Seq Term)
viewFunElims (ObjFunElim lam arg) =
  let (lam', args) = viewFunElims lam
  in (lam', args |> arg)
viewFunElims (MetaFunElim lam arg) =
  let (lam', args) = viewFunElims lam
  in (lam', args |> arg)
viewFunElims e = (e, mempty)

viewMetaFunElims :: Term -> (Term, Seq Term)
viewMetaFunElims (MetaFunElim lam arg) =
  let (lam', args) = viewMetaFunElims lam
  in (lam', args |> arg)
viewMetaFunElims e = (e, mempty)

pattern MetaFunElims lam args <- (viewMetaFunElims -> (lam, args))