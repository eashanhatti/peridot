module Parser where

import Text.Megaparsec hiding(State, SourcePos)
import Text.Megaparsec.Char
import Text.Megaparsec.Error
import Syntax.Surface
import Syntax.Common hiding(CStatement(..), RigidTerm(..), Declaration(..))
import Data.Void
import Data.Text hiding(singleton, empty)
import Control.Monad.Combinators
import Control.Monad.State
import Data.Sequence hiding(empty)
import Data.Maybe
import Extra

keywords =
  [ "Function", "function", "Type", "let", "in", "Bool", "true", "false", "Record"
  , "record", "if", "else", "returns", "Equal", "reflexive", "patch" ]

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
passMethod = try (string "implicit" *> pure Unification)

objPi :: Parser Term
objPi = do
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
  string "->"; ws
  outTy <- prec0
  let
    go :: [(PassMethod, Maybe NameAst, TermAst)] -> Term
    go [(pm, name, inTy)] =
      ObjPi pm (fromMaybe (NameAst Unbound) name) inTy outTy
    go ((pm, name, inTy) : inTys) =
      ObjPi pm (fromMaybe (NameAst Unbound) name) inTy (TermAst (go inTys))
  pure (go inTys)

objLam :: Parser Term
objLam = do
  string "function"; ws
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
  pure (ObjLam (fromList ns) body)

app :: Parser Term
app = do
  lam <- prec1; ws
  char '('; ws
  args <-
    sepBy1
      (do
        pm <- fromMaybe Explicit <$> optional passMethod; ws
        arg <- prec0
        pure (pm, arg))
      commaWs
  char ')'
  pure (App lam (fromList args))

var :: Parser Term
var = do
  n <- some nameChar
  when (elem n keywords) empty
  pure (App (TermAst . Var . UserName . pack $ n) mempty)

objUniv :: Parser Term
objUniv = do
  string "Type"
  pure OUniv

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
  ty <- optional do
    string "returns"; ws
    e <- prec0; ws
    pure e
  char '{'; ws
  body1 <- prec0; ws
  char '}'; ws
  string "else"; ws
  char '{'; ws
  body2 <- prec0; ws
  char '}'
  pure (Case cond ty body1 body2)

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
  str <- prec2; ws
  char '.'; ws
  n <- name
  pure (Select str n)

prec2 :: Parser TermAst
prec2 = do
  pos <- getSourcePos
  e <-
    try objUniv <|>
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
      try objPi <|>
      try objLam <|>
      try app <|>
      equal
    pure (SourcePos (TermAst e) pos)) <|>
  prec1

decl :: Parser DeclarationAst
decl = do
  did <- freshId
  pos <- getSourcePos
  d <- define
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

toplevel :: Parser TermAst
toplevel = do
  ds <- many (decl <* ws <* char ';' <* ws)
  pure (TermAst (Let (fromList ds) (TermAst OUniv)))

parse :: Text -> Either String TermAst
parse text =
  case
      fst .
      flip runState 0 .
      runParserT (ws *> toplevel >>= \e -> ws *> eof *> pure e) "<TODO>" $
      text
    of
    Right term -> Right term
    Left err -> Left (errorBundlePretty err)
