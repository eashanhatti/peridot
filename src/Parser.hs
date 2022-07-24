module Parser where

import Text.Megaparsec hiding(State, SourcePos, parse)
import Text.Megaparsec.Char
import Text.Megaparsec.Error
import Syntax.Surface
import Syntax.Common hiding(CStatement(..), RigidTerm(..), Declaration(..))
import Syntax.Common qualified as Cm
import Data.Void
import Data.Text hiding(singleton, empty, foldr, foldl')
import Data.Text.IO as TIO
import Control.Monad.Combinators
import Data.Foldable
import Control.Monad.State
import Control.Monad.Reader
import Data.Set qualified as Set
import Data.Sequence hiding(empty)
import Data.Maybe
import Extras
import Data.List qualified as L
import System.Directory
import System.FilePath

keywords =
  [ "Fun", "fun", "Type", "let", "in", "Bool", "true", "false"
  , "Struct", "struct", "if", "else", "elif", "Equal", "refl", "patch"
  , "MetaType", "forall", "Exists", "Implies", "And", "Or", "Text", "def"
  , "metadef", "axiom", "output", "query", "metavar", "Code", "Prop"
  , "prop", "Name", "minffun", "mfun" ]

keyword :: Parser ()
keyword = do
  s <- some nameChar
  if elem s keywords then
    pure ()
  else
    empty

ws :: Parser ()
ws =
  void (many 
    (try (void (char ' ')) <|>
    try (void (char '\n')) <|>
    try (void (char '\r')) <|>
    try (void (char '\t')) <|>
    comment))

wsNc :: Parser ()
wsNc =
  void (many
    (try (char ' ') <|>
    try (char '\n') <|>
    try (char '\r') <|>
    char '\t'))

comment :: Parser ()
comment = void do
  string "/*"
  many do
    notFollowedBy (string "*/")
    anySingle
  string "*/"

commaWs :: Parser ()
commaWs = void (ws *> char ',' *> ws)

ampWs :: Parser ()
ampWs = void (ws *> char '&' *> ws)

barWs :: Parser ()
barWs = void (ws *> char '|' *> ws)

semiWs :: Parser ()
semiWs = void (ws *> char ';' *> ws)

nameChar = (try alphaNumChar <|> char '_')

data ParseState = ParseState
  { unNextId :: Id
  , unImported :: Set.Set FilePath }

type Parser a = ParsecT Void Text (StateT ParseState (ReaderT FilePath IO)) a

name :: Parser NameAst
name = do
  s <- some nameChar
  pure (NameAst (UserName (pack s)))

freshId :: Parser Id
freshId = do
  did <- unNextId <$> get
  modify (\st -> st { unNextId = unNextId st + 1 })
  pure did

passMethod :: Parser PassMethod
passMethod =
  try (string "inf" *> pure Unification) <|>
  string "dontcare" *> pure DontCare

piE ::
  Text ->
  (PassMethod -> NameAst -> TermAst -> TermAst -> Term) ->
  Parser Term
piE s c = do
  string s; ws
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
      c pm (fromMaybe (NameAst Unbound) name) inTy outTy
    go ((pm, name, inTy) : inTys) =
      c pm (fromMaybe (NameAst Unbound) name) inTy (TermAst (go inTys))
  pure (go inTys)

propE :: Parser Term
propE = do
  string "Prop"; ws
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
  let
    go :: [(PassMethod, Maybe NameAst, TermAst)] -> Term
    go [(pm, name, inTy)] =
      MetaPi pm (fromMaybe (NameAst Unbound) name) inTy (TermAst MUniv)
    go ((pm, name, inTy) : inTys) =
      MetaPi pm (fromMaybe (NameAst Unbound) name) inTy (TermAst (go inTys))
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

hoasLam :: Parser Term
hoasLam = do
  string "mfun"
  n <- some digitChar
  char '('; ws
  f <- prec0; ws
  char ')'
  pure (HOASObjLam Explicit (read n) f)

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
        pm <- fromMaybe Explicit <$> optional (string "ex" *> pure Unification); ws
        arg <- prec0
        pure (pm, arg))
      commaWs
  char ')'
  pure (App lam' (fromList args))

quant = do
  r <- optional (char '`')
  case r of
    Just _ -> pure Im
    Nothing -> pure Ex

var :: Parser Term
var = do
  q <- quant
  n <- some nameChar
  when (elem n keywords) empty
  pure (App (TermAst . Var q . UserName . pack $ n) mempty)

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
  string "refl"
  pure Refl

sig :: Parser Term
sig = do
  string "Struct"; ws
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
  string "struct"; ws
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
  s <- many (notFollowedBy "\"" *> ((string "\\n" *> pure '\n') <|> anySingle))
  char '"'
  pure (TextLiteral (pack s))

tAppend :: Parser Term
tAppend = do
  SourcePos (TermAst e) _ <- prec1
  es <- some (ws *> string "++" *> ws *> prec1)
  pure (foldl' (\acc e -> TextAppend (TermAst acc) e) e es)

hole :: Parser Term
hole = do
  char '?'
  pure Hole

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
    try hole <|>
    (do
      char '('; ws
      SourcePos (TermAst e) pos <- prec0; ws
      char ')'
      pure e)
  pure (SourcePos (TermAst e) pos)

prec1 :: Parser TermAst
prec1 =
  (do
    pos <- getSourcePos
    e <-
      try select <|>
      try spliceObj
    pure (SourcePos (TermAst e) pos)) <|>
  prec2

prec0 :: Parser TermAst
prec0 =
  try (do
    pos <- getSourcePos
    e <-
      try tAppend <|>
      try (piE "Fun" ObjPi) <|>
      try (piE "MetaFun" MetaPi) <|>
      try (piE "forall" MetaPi) <|>
      try propE <|>
      try quoteObj <|>
      try hoasLam <|>
      try (lam "fun" ObjLam) <|>
      try (lam "metafun" (\ps -> MetaLam (fmap snd ps))) <|>
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
    try prop <|>
    try output <|>
    try rel <|>
    axiom
  pure (SourcePos (DeclAst d did) pos)

define :: Parser Declaration
define = do
  string "def"; ws
  n <- name; ws
  char ':'; ws
  ty <- prec0; ws
  char '='; ws
  def <- prec0
  pure (ObjTerm n ty def)

metadefine :: Parser Declaration
metadefine = do
  string "metadef"; ws
  n <- name; ws
  char ':'; ws
  ty <- prec0; ws
  char '='; ws
  def <- prec0
  pure (MetaTerm n ty def)

rel :: Parser Declaration
rel = do
  string "axiom"; ws
  n <- name; ws
  char ':'; ws
  hd <- prec0; ws
  string ":-"; ws
  as <- sepBy1
    prec0
    (notFollowedBy (ws *> (void (try keyword) <|> eof)) *> commaWs)
  let p = foldl' (\acc q -> TermAst (ImplProp q acc)) hd as
  -- let !_ = tracePretty p
  pure (Axiom n p)

prop :: Parser Declaration
prop = do
  string "prop"; ws
  n <- name; ws
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
  let
    go :: [(PassMethod, Maybe NameAst, TermAst)] -> Term
    go [(pm, name, inTy)] =
      MetaPi pm (fromMaybe (NameAst Unbound) name) inTy (TermAst MUniv)
    go ((pm, name, inTy) : inTys) =
      MetaPi pm (fromMaybe (NameAst Unbound) name) inTy (TermAst (go inTys))
  pure (Axiom n (TermAst (go inTys)))

axiom :: Parser Declaration
axiom = do
  string "axiom"; ws
  n <- name; ws
  char ':'; ws
  ty <- prec0
  pure (Axiom n ty)

proof :: Parser Declaration
proof = do
  string "query"; ws
  ty <- prec0
  pure (Prove ty)

fresh :: Parser Declaration
fresh = do
  string "metavar"; ws
  n <- name; ws
  char ':'; ws
  ty <- prec0
  pure (Fresh n ty)

path :: Parser String
path = L.intercalate "/" <$>
  sepBy1
    (some (nameChar <|> char '.'))
    (notFollowedBy (char '\n') *> char '/')

output :: Parser Declaration
output = do
  string "output"; ws
  n <- path; ws
  e <- prec0
  pure (Output n e)

decls :: Parser (Seq DeclarationAst)
decls = do
  ps <- many (include <* ws)
  dss <- forM ps \p -> do
    imported <- unImported <$> get
    afp <- ask
    let fullPath = afp <> p
    if Set.member fullPath imported then do
      pure mempty
    else do
      s <- liftIO (TIO.readFile fullPath)
      ndid <- unNextId <$> get
      r <- liftIO (parse' ndid decls fullPath (Set.insert fullPath imported) s)
      case r of
        Right (tl, ndid', is) -> do
          modify (\st -> st
            { unNextId = ndid'
            , unImported = Set.insert fullPath is })
          pure tl
        Left e -> fail e
  ds <- many (decl <* ws)
  pure (foldl' (<>) mempty dss <> fromList ds)

toplevel :: Parser TermAst
toplevel = do
  ds <- decls
  pure (TermAst (Let ds (TermAst OUniv)))

include :: Parser FilePath
include = do
  string "import"
  many (char ' ')
  path


parse :: Parser a -> FilePath -> Text -> IO (Either String a)
parse p fn text = fmap (fmap (\(x, _, _) -> x)) (parse' 0 p fn mempty text)

parse' :: Id -> Parser a -> FilePath -> Set.Set FilePath -> Text -> IO (Either String (a, Id, Set.Set FilePath))
parse' idid p fn iis text = do
  afn <- makeAbsolute fn
  (r, ParseState did is) <-
    flip runReaderT (dropFileName afn) .
    flip runStateT (ParseState idid iis) .
    runParserT
      (do
        ws
        e <- p
        ws
        eof
        pure e)
      fn $
    text
  pure case r of
    Right term -> Right (term, did, is)
    Left err -> Left (errorBundlePretty err)
