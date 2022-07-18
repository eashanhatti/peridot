module Syntax.Common where

import Numeric.Natural
import Data.Text
import Data.Hashable
import GHC.Generics
import Data.Map qualified as Map
import Data.Sequence

data PassMethod = Explicit | Unification | DontCare
  deriving (Eq, Show)

data Universe = Meta | Obj
  deriving (Eq, Show)

newtype Field = Field { unField :: Text }
  deriving (Eq, Show)

nameToField (UserName name) = Field name
fieldToName (Field name) = UserName name

newtype Index = Index { unIndex :: Natural }
  deriving (Num, Eq, Ord, Enum, Real, Integral, Show)

newtype Level = Level { unLevel :: Natural }
  deriving (Num, Eq, Enum, Show, Ord)

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

pattern NameIntro univ did <- RNameIntro _ univ did

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
  | NameType Universe a
  | RNameIntro Name Universe Id
  | MetaConstIntro Id
  | CodeObjType a
  | CodeObjIntro a
  | TextType
  | TextIntroNil
  | TextIntroCons Char a
  | HOASObjFunIntro a
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
  | Dummy
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic)
