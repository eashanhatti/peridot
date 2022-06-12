module Parser where

import Text.Megaparsec hiding(State, SourcePos)
import Text.Megaparsec.Char
import Text.Megaparsec.Error
import Syntax.Surface
import Syntax.Common hiding(CStatement(..), RigidTerm(..), Declaration(..))
import Syntax.Common qualified as Cm
import Data.Void
import Data.Text hiding(singleton, empty, foldr, foldl')
import Control.Monad.Combinators
import Data.Foldable
import Control.Monad.State
import Data.Sequence hiding(empty)
import Data.Maybe
import Extra

keywords =
  [ "Function", "function", "Type", "let", "in", "Bool", "true", "false"
  , "Record", "record", "if", "else", "elseif", "Equal", "reflexive", "patch"
  , "MetaType", "Forall", "Exists", "Implies", "And", "Or", "CType", "MNil"
  , "mnil", "C_Int", "C_Stmt", "c_return", "c_break", "c_end", "Code"
  , "CCode"]

ws :: Parser ()
ws =
  void (many 
    (try (void (char ' ')) <|>
    try (void (char '\n')) <|>
    try (void (char '\r')) <|>
    try (void (char '\t')) <|>
    comment))

comment :: Parser ()
comment = void do
  string "/*"
  many do
    notFollowedBy (string "*/")
    anySingle
  string "*/"

commaWs :: Parser ()
commaWs = void (ws *> char ',' *> ws)

semiWs :: Parser ()
semiWs = void (ws *> char ';' *> ws)

nameChar = (try alphaNumChar <|> char '_')

type Parser a = ParsecT Void Text (State Id) a

name :: Parser NameAst
name = do
  s <- some nameChar
  pure (NameAst (UserName (pack s)))

freshId :: Parser Id
freshId = do
  did <- get
  modify (+1)
  pure did

passMethod :: Parser PassMethod
passMethod = try (string "inferred" *> pure Unification)

piE ::
  Text ->
  (PassMethod -> NameAst -> TermAst -> TermAst -> Term) ->
  Parser Term
piE s c = do
  string "Function"; ws
  char '('; ws
  inTys <-
    sepBy1
      (try (do
        pm <- optional passMethod; ws
        n <- name; ws
        char ':'; ws
        ty <- prec0
        pure (fromMaybe Explicit pm, Just n, ty))
      <|> (do
        ty <- prec0
        pure (Explicit, Nothing, ty)))
      commaWs
  char ')'; ws
  string s; ws
  outTy <- prec0
  let
    go :: [(PassMethod, Maybe NameAst, TermAst)] -> Term
    go [(pm, name, inTy)] =
      c pm (fromMaybe (NameAst Unbound) name) inTy outTy
    go ((pm, name, inTy) : inTys) =
      c pm (fromMaybe (NameAst Unbound) name) inTy (TermAst (go inTys))
  pure (go inTys)

lam ::
  Text ->
  (Seq (PassMethod, NameAst) -> TermAst -> Term) ->
  Parser Term
lam s c = do
  string s; ws
  char '('; ws
  ns <-
    sepBy
      (do
        pm <- fromMaybe Explicit <$> optional passMethod; ws
        n <- name
        pure (pm, n))
      commaWs
  char ')'; ws
  string "=>"; ws
  body <- prec0
  pure (c (fromList ns) body)

app :: Parser Term
app = do
  lam <- prec1; ws
  let
    lam' =
      case lam of
        SourcePos (TermAst (App e Empty)) _ -> e
        _ -> lam
  char '('; ws
  args <-
    sepBy1
      (do
        pm <-
          fromMaybe
            Explicit <$>
            optional (string "explicit" *> pure Unification); ws
        arg <- prec0
        pure (pm, arg))
      commaWs
  char ')'
  pure (App lam' (fromList args))

var :: Parser Term
var = do
  n <- some nameChar
  when (elem n keywords) empty
  pure (App (TermAst . Var . UserName . pack $ n) mempty)

objUniv :: Parser Term
objUniv = do
  string "Type"
  pure OUniv

metaUniv :: Parser Term
metaUniv = do
  string "MetaType"
  pure MUniv

liftObj :: Parser Term
liftObj = do
  string "Code"; ws
  char '('; ws
  e <- prec0; ws
  char ')'
  pure (LiftObj e)

quoteObj :: Parser Term
quoteObj = do
  char '<'; ws
  e <- prec0; ws
  char '>'
  pure (QuoteObj e)

spliceObj :: Parser Term
spliceObj = do
  char '~'; ws
  e <- prec2; ws
  pure (SpliceObj e)

liftC :: Parser Term
liftC = do
  string "CCode"; ws
  char '('; ws
  e <- prec0; ws
  char ')'
  pure (LiftC e)

quoteC :: Parser Term
quoteC = do
  string "c<"; ws
  e <- prec0; ws
  char '>'
  pure (QuoteC e)

spliceC :: Parser Term
spliceC = do
  string "c~"; ws
  e <- prec2; ws
  pure (SpliceC e)

cUniv :: Parser Term
cUniv = do
  string "CType"
  pure LCUniv

letE :: Parser Term
letE = do
  string "let"; ws
  char '{'; ws
  ds <- many (decl <* ws <* char ';' <* ws)
  char '}'; ws
  string "in"; ws
  char '{'; ws
  body <- prec0; ws
  char '}'
  pure (Let (fromList ds) body)

bool :: Parser Term
bool = do
  string "Bool"
  pure Bool

true :: Parser Term
true = do
  string "true"
  pure BTrue

false :: Parser Term
false = do
  string "false"
  pure BFalse

ifE :: Parser Term
ifE = do
  string "if"; ws
  cond <- prec0; ws
  char '{'; ws
  body1 <- prec0; ws
  char '}'; ws
  elifs <- many do
    string "elseif"; ws
    cond <- prec0; ws
    char '{'; ws
    body <- prec0; ws
    char '}'; ws
    pure (cond, body)
  string "else"; ws
  char '{'; ws
  body2 <- prec0; ws
  char '}'
  pure
    (Case
      cond
      body1
      (foldr (\(c, b1) b2 -> TermAst (Case c b1 b2)) body2 elifs))

equal :: Parser Term
equal = do
  string "Equal"; ws
  char '('; ws
  x <- prec0
  commaWs
  y <- prec0; ws
  char ')'
  pure (Equal x y)

refl :: Parser Term
refl = do
  string "reflexive"
  pure Refl

sig :: Parser Term
sig = do
  string "Record"; ws
  char '{'; ws
  tys <-
    sepBy
      (do
        n <- name; ws
        char ':'; ws
        ty <- prec0; ws
        pure (n, ty))
      commaWs; ws
  char '}'
  pure (Sig (fromList tys))

struct :: Parser Term
struct = do
  string "record"; ws
  char '{'; ws
  defs <-
    sepBy
      (do
        n <- name; ws
        char '='; ws
        def <- prec0; ws
        pure (n, def))
      commaWs; ws
  char '}'
  pure (Struct (fromList defs))

patch :: Parser Term
patch = do
  string "patch"; ws
  str <- prec0; ws
  char '{'; ws
  defs <-
    sepBy
      (do
        n <- name; ws
        char '='; ws
        def <- prec0; ws
        pure (n, def))
      commaWs; ws
  char '}'
  pure (Patch str (fromList defs))

select :: Parser Term
select = do
  SourcePos (TermAst str) _ <- prec2
  fds <- some (char '.' *> name)
  pure (foldl' (\e fd -> Select (TermAst e) fd) str fds)

implProp :: Parser Term
implProp = do
  string "Implies"; ws
  char '('; ws
  p <- prec0
  commaWs
  q <- prec0
  char ')'
  pure (ImplProp p q)

conjProp :: Parser Term
conjProp = do
  string "And"; ws
  char '('; ws
  p <- prec0
  commaWs
  q <- prec0
  char ')'
  pure (ConjProp p q)

disjProp :: Parser Term
disjProp = do
  string "Or"; ws
  char '('; ws
  p <- prec0
  commaWs
  q <- prec0
  char ')'
  pure (DisjProp p q)

forallProp :: Parser Term
forallProp = do
  string "Forall"; ws
  n <- name; ws
  char ','; ws
  p <- prec0
  pure (ForallProp (TermAst (MetaLam (singleton n) p)))

existsProp :: Parser Term
existsProp = do
  string "Exists"; ws
  n <- name; ws
  char ','; ws
  p <- prec0
  pure (ExistsProp (TermAst (MetaLam (singleton n) p)))

listTyNil :: Parser Term
listTyNil = parens do
  string "MNil"
  pure ListTypeNil

listTyCons :: Parser Term
listTyCons = parens do
  string "MCons"; ws
  x <- prec0; ws
  l <- prec0; ws
  pure (ListTypeCons x l)

listNil :: Parser Term
listNil = parens do
  string "mnil"
  pure ListNil

listCons :: Parser Term
listCons = parens do
  string "mcons"; ws
  e <- prec0; ws
  l <- prec0; ws
  pure (ListCons e l)

cIntTy :: Parser Term
cIntTy = do
  string "C_Int"
  pure CIntType

cInt :: Parser Term
cInt = parens do
  string "c_int"; ws
  x <- some digitChar
  pure (CInt (read x))

cPtrTy :: Parser Term
cPtrTy = parens do
  string "C_Ptr"; ws
  ty <- prec0
  pure (CPtrType ty)

cLValTy :: Parser Term
cLValTy = parens do
  string "C_LVal"; ws
  ty <- prec0
  pure (CLValType ty)

cStmtTy :: Parser Term
cStmtTy = do
  string "C_Stmt"
  pure CStmtType

cReturn :: Parser Term
cReturn = do
  string "c_return"
  pure CReturn

cIf :: Parser Term
cIf = parens do
  string "c_if"; ws
  cond <- prec0; ws
  body1 <- prec0; ws
  body2 <- prec0
  pure (CIf cond body1 body2)

cWhile :: Parser Term
cWhile = parens do
  string "c_while"; ws
  cond <- prec0; ws
  body <- prec0
  pure (CWhile cond body)

cBreak :: Parser Term
cBreak = do
  string "c_break"
  pure CBreak

cAssign :: Parser Term
cAssign = parens do
  string "c_assign"; ws
  var <- prec0; ws
  val <- prec0
  pure (CAssign var val)

cStructTy :: Parser Term
cStructTy = parens do
  string "C_Struct"; ws
  ty <- prec0
  pure (CStructType ty)

cStruct :: Parser Term
cStruct = parens do
  string "c_struct"; ws
  e <- prec0
  pure (CStruct e)

cApp :: Parser Term
cApp = parens do
  string "c_apply"; ws
  lam <- prec0; ws
  args <- prec0
  pure (CApp lam args)

cAdd :: Parser Term
cAdd = parens do
  string "c_add"; ws
  x <- prec0; ws
  y <- prec0
  pure (CAdd x y)

cSeq :: Parser Term
cSeq = parens do
  string "c_seq"; ws
  s1 <- prec0; ws
  s2 <- prec0
  pure (CSeq s1 s2)

cDeclVar :: Parser Term
cDeclVar = parens do
  string "c_var"; ws
  ty <- prec0; ws
  cont <- prec0
  pure (CDeclVar ty cont)

cEq :: Parser Term
cEq = parens do
  string "c_eq"; ws
  x <- prec0; ws
  y <- prec0
  pure (CEq x y)

cRef :: Parser Term
cRef = parens do
  string "c_ref"; ws
  e <- prec0
  pure (CRef e)

cDerefL :: Parser Term
cDerefL = parens do
  string "c_derefL"; ws
  e <- prec0
  pure (CDerefLVal e)

cDerefR :: Parser Term
cDerefR = parens do
  string "c_derefR"; ws
  e <- prec0
  pure (CDerefRVal e)

cCast :: Parser Term
cCast = parens do
  string "c_cast"; ws
  ty <- prec0; ws
  e <- prec0
  pure (CCast ty e)

cLam :: Parser Term
cLam = parens do
  string "c_fun"; ws
  body <- prec0
  pure (CLam body)

cLamTy :: Parser Term
cLamTy = parens do
  string "C_Fun"; ws
  ty <- prec0
  pure (CLamType ty)

parens :: Parser a -> Parser a
parens p = do
  char '['; ws
  r <- p; ws
  char ']'
  pure r

defineE :: Parser Term
defineE = parens do
  string "p_define"; ws
  n <- prec0; ws
  def <- prec0; ws
  cont <- prec0
  pure (Define n def cont)

declare :: Parser Term
declare = parens do
  string "p_declare"; ws
  n <- prec0; ws
  ty <- prec0; ws
  cont <- prec0
  pure (Declare n ty cont)

cDefine :: Parser Term
cDefine = parens do
  string "c_define"; ws
  n <- prec0; ws
  def <- prec0; ws
  cont <- prec0
  pure (CDefine n def cont)

cDeclare :: Parser Term
cDeclare = parens do
  string "c_declare"; ws
  n <- prec0; ws
  ty <- prec0; ws
  cont <- prec0
  pure (CDeclare n ty cont)

objNameTy :: Parser Term
objNameTy = do
  string "Name"; ws
  char '('; ws
  ty <- prec0; ws
  char ')'
  pure (NameType Cm.Obj ty)

cNameTy :: Parser Term
cNameTy = do
  string "CName"; ws
  char '('; ws
  ty <- prec0; ws
  char ')'
  pure (NameType Cm.Obj ty)

prec2 :: Parser TermAst
prec2 = do
  pos <- getSourcePos
  e <-
    try objUniv <|>
    try metaUniv <|>
    try cUniv <|>
    try bool <|>
    try true <|>
    try false <|>
    try var <|>
    try ifE <|>
    try sig <|>
    try refl <|>
    try struct <|>
    try patch <|>
    try letE <|>
    try listTyNil <|>
    try listTyCons <|>
    try listNil <|>
    try listCons <|>
    try cIntTy <|>
    try cInt <|>
    try cPtrTy <|>
    try cLValTy <|>
    try cStmtTy <|>
    try cReturn <|>
    try cIf <|>
    try cWhile <|>
    try cBreak <|>
    try cAssign <|>
    try cStructTy <|>
    try cStruct <|>
    try cApp <|>
    try cAdd <|>
    try cSeq <|>
    try cDeclVar <|>
    try cEq <|>
    try cRef <|>
    try cDerefL <|>
    try cDerefR <|>
    try cCast <|>
    try cLam <|>
    try cLamTy <|>
    try cNameTy <|>
    try objNameTy <|>
    try defineE <|>
    try declare <|>
    try cDefine <|>
    try cDeclare <|>
    (do
      char '('; ws
      SourcePos (TermAst e) pos <- try prec1 <|> prec0; ws
      char ')'
      pure e)
  pure (SourcePos (TermAst e) pos)

prec1 :: Parser TermAst
prec1 =
  (do
    pos <- getSourcePos
    e <-
      try select <|>
      try spliceObj <|>
      try spliceC <|>
      (do
        char '('; ws
        SourcePos (TermAst e) pos <- prec0; ws
        char ')'
        pure e)
    pure (SourcePos (TermAst e) pos)) <|>
  prec2

prec0 :: Parser TermAst
prec0 =
  try (do
    pos <- getSourcePos
    e <-
      try (piE "->" ObjPi) <|>
      try (piE "~>" MetaPi) <|>
      try forallProp <|>
      try existsProp <|>
      try quoteObj <|>
      try quoteC <|>
      try (lam "function" ObjLam) <|>
      try (lam "metafunction" (\ps -> MetaLam (fmap snd ps))) <|>
      try app <|>
      try equal <|>
      try liftObj <|>
      try liftC <|>
      try implProp <|>
      try conjProp <|>
      disjProp
    pure (SourcePos (TermAst e) pos)) <|>
  prec1

decl :: Parser DeclarationAst
decl = do
  did <- freshId
  pos <- getSourcePos
  d <-
    try define <|>
    try metadefine <|>
    try cdefine <|>
    try proof <|>
    try fresh <|>
    axiom
  pure (SourcePos (DeclAst d did) pos)

define :: Parser Declaration
define = do
  string "define"; ws
  n <- name; ws
  char ':'; ws
  ty <- prec0; ws
  char '='; ws
  def <- prec0
  pure (ObjTerm n ty def)

cdefine :: Parser Declaration
cdefine = do
  string "cdefine"; ws
  n <- name; ws
  char ':'; ws
  ty <- prec0; ws
  char '='; ws
  def <- prec0
  pure (CTerm n ty def)

metadefine :: Parser Declaration
metadefine = do
  string "metadefine"; ws
  n <- name; ws
  char ':'; ws
  ty <- prec0; ws
  char '='; ws
  def <- prec0
  pure (MetaTerm n ty def)

axiom :: Parser Declaration
axiom = do
  string "axiom"; ws
  n <- name; ws
  char ':'; ws
  ty <- prec0
  pure (Axiom n ty)

proof :: Parser Declaration
proof = do
  string "proof"; ws
  ty <- prec0
  pure (Prove ty)

fresh :: Parser Declaration
fresh = do
  string "variable"; ws
  n <- name; ws
  char ':'; ws
  ty <- prec0
  pure (Fresh n ty)

toplevel :: Parser TermAst
toplevel = do
  ds <- many (decl <* ws <* char ';' <* ws)
  pure (TermAst (Let (fromList ds) (TermAst OUniv)))

parse :: Text -> Either String TermAst
parse text =
  case
      fst .
      flip runState 0 .
      runParserT
        (do
          ws
          e <- toplevel
          ws
          eof
          pure e)
        "<TODO>" $
      text
    of
    Right term -> Right term
    Left err -> Left (errorBundlePretty err)
