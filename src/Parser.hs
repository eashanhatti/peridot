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
import Data.List qualified as L

keywords =
  [ "Function", "function", "Type", "let", "in", "Bool", "true", "false"
  , "Record", "record", "if", "else", "elseif", "Equal", "reflexive", "patch"
  , "MetaType", "Forall", "Exists", "Implies", "And", "Or", "Text", "define"
  , "metadefine", "axiom", "#output", "proof", "variable", "Code" ]

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
passMethod =
  try (string "inferred" *> pure Unification) <|>
  string "dontcare" *> pure DontCare

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
        pm <- fromMaybe Explicit <$> optional (string "explicit" *> pure Unification); ws
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

letE :: Parser Term
letE = do
  string "let"; ws
  char '{'; ws
  ds <- many (decl <* ws)
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

defineE :: Parser Term
defineE = parens do
  string "p_define"; ws
  name <- prec2; ws
  def <- prec2; ws
  cont <- prec2
  pure (Define name def cont)

declare :: Parser Term
declare = parens do
  string "p_declare"; ws
  name <- prec2; ws
  ty <- prec2; ws
  cont <- prec2
  pure (Declare name ty cont)

parens p = do
  string "["; ws
  x <- p; ws
  string "]"
  pure x

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
  char '('; ws
  ns <-
    sepBy1
      (do
        n <- name; ws
        char ':'; ws
        ty <- prec0
        pure (n, ty))
      commaWs; ws
  char ')'
  char ','; ws
  p <- prec0
  let TermAst e = foldr (\(n, ty) acc -> TermAst (ForallProp n ty acc)) p ns
  pure e

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

textTy :: Parser Term
textTy = do
  string "Text"
  pure Text

text :: Parser Term
text = do
  char '"'
  s <- many (notFollowedBy "\"" *> (anySingle <|> (string "\\n" *> pure '\n')))
  char '"'
  pure (TextLiteral (pack s))

tAppend :: Parser Term
tAppend = do
  SourcePos (TermAst e) _ <- prec2
  es <- some (ws *> string "++" *> ws *> prec2)
  pure (foldl' (\acc e -> TextAppend (TermAst acc) e) e es)

prec2 :: Parser TermAst
prec2 = do
  pos <- getSourcePos
  e <-
    try objUniv <|>
    try metaUniv <|>
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
    try objNameTy <|>
    try defineE <|>
    try declare <|>
    try textTy <|>
    try text <|>
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
      try tAppend <|>
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
      -- try existsProp <|>
      try quoteObj <|>
      try (lam "function" ObjLam) <|>
      try (lam "metafunction" (\ps -> MetaLam (fmap snd ps))) <|>
      try app <|>
      try equal <|>
      try liftObj <|>
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
    try proof <|>
    try fresh <|>
    try output <|>
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

path :: Parser String
path = L.intercalate "/" <$> sepBy1 (some (nameChar <|> char '.')) (char '/')

output :: Parser Declaration
output = do
  string "#output"; ws
  n <- path; ws
  e <- prec0
  pure (Output n e)

toplevel :: Parser TermAst
toplevel = do
  ds <- many (decl <* ws)
  pure (TermAst (Let (fromList ds) (TermAst OUniv)))

parse :: Parser a -> String -> Text -> Either String a
parse p fn text =
  case
      fst .
      flip runState 0 .
      runParserT
        (do
          ws
          e <- p
          ws
          eof
          pure e)
        fn $
      text
    of
    Right term -> Right term
    Left err -> Left (errorBundlePretty err)