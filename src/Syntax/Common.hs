module Syntax.Common where

import Numeric.Natural
import Data.Text
import Data.Hashable
import GHC.Generics
import Data.Map qualified as Map
import Data.Sequence

data PassMethod = Explicit | Unification
  deriving (Eq, Show)

data Universe = Meta | Obj | LowC | List
  deriving (Eq, Show)

newtype Field = Field { unField :: Text }
  deriving (Eq, Show)

nameToField (UserName name) = Field name
fieldToName (Field name) = UserName name

newtype Index = Index { unIndex :: Natural }
  deriving (Num, Eq, Ord, Enum, Real, Integral, Show)

newtype Level = Level { unLevel :: Natural }
  deriving (Num, Eq, Enum, Show)

newtype Id = Id { unId :: Natural }
  deriving (Eq, Ord, Generic, Num, Enum, Real, Integral, Show)

data Global
  = UVGlobal Natural
  | LVGlobal Natural
  deriving (Eq, Ord, Show)

unGlobal (UVGlobal n) = n
unGlobal (LVGlobal n) = n

instance Hashable Id

data Name = UserName Text | MachineName Natural | Unbound
  deriving (Eq, Ord, Show)

data RigidTerm a
  -- Object level
  = TwoType
  | TwoIntro0
  | TwoIntro1
  | SingType a a
  | SingIntro a
  | ObjIdType a a
  | ObjIdIntro a
  -- Meta level
  | NameCType a
  | NameCIntro Id
  | NameObjType a
  | NameObjIntro Id
  | MetaConstIntro Id
  | CodeObjType a
  | CodeObjIntro a
  | CodeCType a
  | CodeCIntro a
  | ListTypeNil
  | ListTypeCons a a
  | ListIntroNil
  | ListIntroCons a a
  | CLValType a
  | CIntType
  | CPtrType a
  | CStmtType
  | CStmtIntroRet
  | CStmtIntroIf a a a
  | CStmtIntroWhl a a
  | CStmtIntroBrk
  | CStmtIntroCall a a
  | CStmtIntroSeq a a -- sequencing
  | CStmtIntroBind a a -- variable binding
  | CStmtIntroSet a a
  | CStructType a
  | CFunType a
  | CFunIntro a
  | CIntIntro Int
  | CIntElimAdd a a
  | CIntElimEq a a
  | CPtrIntro a
  | CPtrElimRVal a
  | CPtrElimLVal a
  | CStructIntro a
  | CCast a a
  | CDeclare a a a -- ty, name, cont
  | CDefine a a a -- name, def, cont
  -- Propositions
  | PropConstIntro Id
  | ImplType a a
  | ConjType a a
  | DisjType a a
  | AllType a
  | SomeType a
  | PropIdType a a
  -- Other
  | TypeType Universe
  | ElabError
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic)

data Declaration a
  = MetaConst Id a
  | ObjTerm Id a a -- sig, def
  | MetaTerm Id a a -- sig, def
  | CTerm Id a a -- sig, def
  | DElabError
  deriving (Eq, Show, Functor, Foldable, Traversable)
