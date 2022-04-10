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
import GHC.Exts

keywords = ["let", "in", "Type", "qUnit"]

ws = many (try (char ' ') <|> try (char '\n') <|> try (char '\r') <|> char '\t')

nameChar = (try alphaNumChar <|> char '_')

type Parser a = ParsecT Void Text (State Id) a

name :: Parser NameAst
name = do
  s <- some nameChar
  pure (NameAst (UserName (pack s)))

objPiTy :: Parser TermAst
objPiTy = do
  string "'["; ws
  n <- name; ws
  char ':'; ws
  inTy <- term; ws
  char ']'; ws
  string "->"; ws
  outTy <- term
  pure (TermAst (ObjPi n inTy outTy))

metaPiTy :: Parser TermAst
metaPiTy = do
  string "["; ws
  n <- name; ws
  char ':'; ws
  inTy <- term; ws
  char ']'; ws
  string "->"; ws
  outTy <- term
  pure (TermAst (MetaPi n inTy outTy))

metaLam :: Parser TermAst
metaLam = do
  char '\\'; ws
  ns <- some do
    n <- name; ws
    pure n
  char '{'; ws
  body <- term; ws
  char '}'
  pure (TermAst (MetaLam ns body))

objLam :: Parser TermAst
objLam = do
  string "'\\"; ws
  ns <- some do
    n <- name; ws
    pure n
  char '{'; ws
  body <- term; ws
  char '}'
  pure (TermAst (ObjLam ns body))

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

objUniv :: Parser TermAst
objUniv = do
  string "OType"
  pure (TermAst ObjUniv)

metaUniv :: Parser TermAst
metaUniv = do
  string "MType"
  pure (TermAst MetaUniv)

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
  d <- try datatype <|> try metaVal <|> try objVal <|> try axiom <|> try prove <|> fresh
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

metaVal :: Parser DeclarationAst
metaVal = do
  did <- freshId
  string "val"; ws
  n <- name; ws
  char ':'; ws
  sig <- term; ws
  char '='; ws
  def <- term
  pure (DeclAst (MetaTerm n sig def) did)

objVal :: Parser DeclarationAst
objVal = do
  did <- freshId
  string "'val"; ws
  n <- name; ws
  char ':'; ws
  sig <- term; ws
  char '='; ws
  def <- term
  pure (DeclAst (ObjTerm n sig def) did)

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

data K = Term | Type

qPi :: Parser TermQuote
qPi = do
  char '('; ws
  string "qpi"; ws
  inTy <- term; ws
  outTy <- term; ws
  char ')'
  pure (QPi inTy outTy)

qUnitType :: Parser TermQuote
qUnitType = do
  string "qUnit"
  pure QUnitType

qLam :: Parser TermQuote
qLam = do
  char '('; ws
  string "qlam"; ws
  body <- term; ws
  char ')'
  pure (QLam body)

qApp :: Parser TermQuote
qApp = do
  char '('; ws
  string "qapp"; ws
  lam <- term; ws
  arg <- term; ws
  char ')'
  pure (QApp lam arg)

quote :: Parser TermAst
quote = do
  q <-
    qPi <|>
    qUnitType <|>
    qLam <|>
    qApp
  pure (TermAst (Quote q))

quoteTy :: Parser TermAst
quoteTy = do
  char '('; ws
  string "Quote"; ws
  ty <- term; ws
  char ')'
  pure (TermAst (QuoteType ty)) 

term :: Parser TermAst
term = do
  pos <- getSourcePos
  e <-
    try metaLam <|>
    try objLam <|>
    try app <|>
    try quote <|>
    try quoteTy <|>
    try objUniv <|>
    try metaUniv <|>
    try letB <|>
    try ioPure <|>
    try ioTy <|>
    try ioBind <|>
    try unitTy <|>
    try unit <|>
    try metaPiTy <|>
    try objPiTy <|>
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
