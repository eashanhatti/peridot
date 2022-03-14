module Parser where

import Text.Megaparsec hiding(State, SourcePos)
import Text.Megaparsec.Char
import Text.Megaparsec.Error
import Syntax.Surface
import Syntax.Extra
import Data.Void
import Data.Text
import Control.Monad.Combinators
import Control.Monad.State

keywords = ["let", "in", "Type"]

ws = many (try (char ' ') <|> try (char '\n') <|> try (char '\r') <|> char '\t')

nameChar = (try alphaNumChar <|> char '_')

type Parser a = ParsecT Void Text (State Id) a

name :: Parser NameAst
name = do
  s <- some nameChar
  pure (NameAst (UserName (pack s)))

piTy :: Parser TermAst
piTy = do
  char '['; ws
  n <- name; ws
  char ':'; ws
  inTy <- term; ws
  char ']'; ws
  string "->"; ws
  outTy <- term
  pure (TermAst (Pi n inTy outTy))

lam :: Parser TermAst
lam = do
  char '\\'; ws
  ns <- some do
    n <- name; ws
    pure n
  char '{'; ws
  body <- term; ws
  char '}'
  pure (TermAst (Lam ns body))

app :: Parser TermAst
app = do
  char '<'; ws
  lam <- term; ws
  args <- some do
    arg <- term; ws
    pure arg
  char '>'
  pure (TermAst (App lam args))

var :: Parser TermAst
var = do
  s <- some nameChar
  when (elem s keywords) (fail "keyword")
  pure (TermAst (Var (UserName (pack s))))

univ :: Parser TermAst
univ = do
  string "Type"
  pure (TermAst Univ)

letB :: Parser TermAst
letB = do
  string "let"; ws
  char '{'; ws
  decls <- many do
    d <- decl; ws
    char ';'; ws
    pure d
  char '}'; ws
  string "in"; ws
  char '{'; ws
  body <- term; ws
  char '}'
  pure (TermAst (Let decls body))

ruleTy :: Parser TermAst
ruleTy = do
  string "rule"; ws
  outTy <- term; ws
  string ":-"; ws
  inTy <- term
  pure (TermAst (Rule outTy inTy))

ioPure :: Parser TermAst
ioPure = do
  char '('; ws
  string "pure"; ws
  x <- term; ws
  char ')'
  pure (TermAst (IOPure x))

ioTy :: Parser TermAst
ioTy = do
  char '('; ws
  string "IO"; ws
  ty <- term; ws
  char ')'
  pure (TermAst (IOType ty))

ioBind :: Parser TermAst
ioBind = do
  char '('; ws
  string "bind"; ws
  act <- op; ws
  k <- term; ws
  char ')'
  pure (TermAst (IOBind act k))

unitTy :: Parser TermAst
unitTy = do
  string "Unit"
  pure (TermAst UnitType)

unit :: Parser TermAst
unit = do
  string "unit"
  pure (TermAst Unit)

decl :: Parser DeclarationAst
decl = do
  pos <- getSourcePos
  d <- try datatype <|> try val <|> try axiom <|> try prove <|> fresh
  pure (SourcePos d pos)

datatype :: Parser DeclarationAst
datatype = do
  did <- freshId
  string "datatype"; ws
  n <- name; ws
  char ':'; ws
  sig <- term; ws
  char '{'; ws
  cs <- many do
    c <- fmap ($ did) con; ws
    char ';'; ws
    pure c
  char '}'; ws
  pure (DeclAst (Datatype n sig cs) did)

val :: Parser DeclarationAst
val = do
  did <- freshId
  string "lazy"; ws
  n <- name; ws
  char ':'; ws
  sig <- term; ws
  char '='; ws
  def <- term
  pure (DeclAst (Term n sig def) did)

axiom :: Parser DeclarationAst
axiom = do
  did <- freshId
  string "assume"; ws
  n <- name; ws
  char ':'; ws
  sig <- term
  pure (DeclAst (Axiom n sig) did)

prove :: Parser DeclarationAst
prove = do
  did <- freshId
  string "prove"; ws
  sig <- term
  pure (DeclAst (Prove sig) did)

fresh :: Parser DeclarationAst
fresh = do
  did <- freshId
  string "fresh"; ws
  n <- name; ws
  char ':'; ws
  sig <- term
  pure (DeclAst (Fresh n sig) did)

con :: Parser (Id -> ConstructorAst)
con = do
  did <- freshId
  n <- name; ws
  char ':'; ws
  sig <- term
  pure (\dtDid -> ConstrAst (Constr n sig) did dtDid)

op :: Parser IOOperation
op = do
  char '('; ws
  string "print"; ws
  c <- alphaNumChar; ws
  char ')'
  pure (PutChar c)

term :: Parser TermAst
term = do
  pos <- getSourcePos
  e <-
    try lam <|>
    try app <|>
    try univ <|>
    try letB <|>
    try ioPure <|>
    try ioTy <|>
    try ioBind <|>
    try unitTy <|>
    try unit <|>
    try piTy <|>
    try var <|>
    ruleTy
  pure (SourcePos e pos)

freshId :: Parser Id
freshId = do
  did <- get
  modify (+1)
  pure did

parse :: Text -> Either String TermAst
parse text =
  case fst . flip runState 0 . runParserT (term >>= \e -> ws *> eof *> pure e) "<TODO>" $ text of
    Right term -> Right term
    Left err -> Left (errorBundlePretty err)
