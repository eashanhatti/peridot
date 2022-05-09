module Parser where

import Text.Megaparsec hiding(State, SourcePos)
import Text.Megaparsec.Char
import Text.Megaparsec.Error
import Syntax.Surface
import Syntax.Common hiding(CStatement(..), RigidTerm(..), Declaration(..))
import Data.Void
import Data.Text hiding(singleton)
import Control.Monad.Combinators
import Control.Monad.State
import Data.Sequence

keywords =
  [ "let", "in", "Type", "cfun", "cif", "else", "var", "quoteL", "spliceLStmt", "quoteC", "spliceC", "LiftC", "rule", "Int"
  , "all", "conj", "disj", "impl", "some", "atomicformula", "Prop"]

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
  pure (TermAst (MetaLam (fromList ns) body))

liftCore :: Parser TermAst
liftCore = do
  char '('; ws
  string "LiftC"; ws
  ty <- term; ws
  char ')'
  pure (TermAst (LiftCore ty))

spliceCore :: Parser TermAst
spliceCore = do
  char '('; ws
  string "spliceC"; ws
  term <- term; ws
  char ')'
  pure (TermAst (SpliceCore term))

quoteCore :: Parser TermAst
quoteCore = do
  char '('; ws
  string "quoteC"; ws
  term <- term; ws
  char ')'
  pure (TermAst (QuoteCore term))

liftLow :: Parser TermAst
liftLow = do
  char '('; ws
  string "LiftL"; ws
  ty <- term; ws
  char ')'
  pure (TermAst (LiftLowCTm ty))

spliceLow :: Parser TermAst
spliceLow = do
  char '('; ws
  string "spliceL"; ws
  term <- term; ws
  char ')'
  pure (TermAst (SpliceLowCTm term))

quoteLow :: Parser TermAst
quoteLow = do
  char '('; ws
  string "quoteL"; ws
  term <- term; ws
  char ')'
  pure (TermAst (QuoteLowCTm term))

objLam :: Parser TermAst
objLam = do
  string "'\\"; ws
  ns <- some do
    n <- name; ws
    pure n
  char '{'; ws
  body <- term; ws
  char '}'
  pure (TermAst (ObjLam (fromList ns) body))

app :: Parser TermAst
app = do
  char '<'; ws
  lam <- term; ws
  args <- some do
    arg <- term; ws
    pure arg
  char '>'
  pure (TermAst (App lam (fromList args)))

var :: Parser TermAst
var = do
  s <- some nameChar
  when (elem s keywords) (fail "keyword")
  pure (TermAst (Var (UserName (pack s))))

metaUniv :: Parser TermAst
metaUniv = do
  string "MType"
  pure (TermAst MUniv)

objUniv :: Parser TermAst
objUniv = do
  string "OType"
  pure (TermAst OUniv)

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
  pure (TermAst (Let (fromList decls) body))

decl :: Parser DeclarationAst
decl = do
  pos <- getSourcePos
  d <-
    try datatype <|>
    try metaVal <|>
    try objVal <|>
    try axiom <|>
    try prove <|>
    try fresh <|>
    cFun
  pure (SourcePos d pos)

block :: Parser CStatement
block = do
  char '{'; ws
  stmts <- fromList <$> many do
    s <- stmt; ws
    char ';'; ws
    pure s
  char '}'
  pure (Block stmts)

ifS :: Parser CStatement
ifS = do
  string "cif"; ws
  cond <- term; ws
  tB <- stmt; ws
  string "else"; ws
  fB <- stmt
  pure (If cond tB fB)

varDecl :: Parser CStatement
varDecl = do
  string "var"; ws
  n <- name; ws
  char ':'; ws
  ty <- term
  pure (VarDecl n ty)

ret :: Parser CStatement
ret = do
  string "return"; ws
  e <- optional term
  pure (Return e)

assign :: Parser CStatement
assign = do
  var <- term; ws
  string "="; ws
  val <- term
  pure (Assign var val)

stmtSplice :: Parser CStatement
stmtSplice = do
  char '('; ws
  string "spliceLStmt"; ws
  quote <- term; ws
  char ')'
  pure (SpliceLowCStmt quote)

stmt :: Parser CStatementAst
stmt = do
  s <-
    try block <|>
    try ifS <|>
    try varDecl <|>
    try ret <|>
    try assign <|>
    stmtSplice
  pure (CStmtAst s)

cFun :: Parser DeclarationAst
cFun = do
  did <- freshId
  string "cfun"; ws
  n <- name; ws
  ps <- do
    char '('
    ps <- fromList <$> sepBy param (ws *> char ',' *> ws); ws
    char ')'; ws
    pure ps
  char ':'; ws
  outTy <- term; ws
  body <- stmt
  pure (DeclAst (CFun n ps outTy body) did)
  where
    param = do
      pn <- name; ws
      char ':'; ws
      ty <- term
      pure (pn, ty)


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
  pure (DeclAst (Datatype n sig (fromList cs)) did)

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

liftLowStmt :: Parser TermAst
liftLowStmt = do
  char '('; ws
  string "LiftLStmt"; ws
  ty <- term; ws
  char ')'
  pure (TermAst (LiftLowCStmt ty))

quoteLowStmt :: Parser TermAst
quoteLowStmt = do
  char '('; ws
  string "quoteLStmt"; ws
  s <- stmt; ws
  char ')'
  pure (TermAst (QuoteLowCStmt s))

cIntTy :: Parser TermAst
cIntTy = do
  string "Int"; ws
  pure (TermAst CIntType)

cVoidTy :: Parser TermAst
cVoidTy = do
  string "Void"; ws
  pure (TermAst CVoidType)

cPtrTy :: Parser TermAst
cPtrTy = do
  char '('; ws
  string "Ptr"; ws
  ty <- term; ws
  char ')'
  pure (TermAst (CPtrType ty))

-- cLValTy :: Parser TermAst
-- cLValTy = do
--   char '('; ws
--   string "LVal"; ws
--   ty <- term; ws
--   char ')'
--   pure (TermAst (CLValType ty))

-- cRValTy :: Parser TermAst
-- cRValTy = do
--   char '('; ws
--   string "RVal"; ws
--   ty <- term; ws
--   char ')'
--   pure (TermAst (CRValType ty))

cRef :: Parser TermAst
cRef = do
  char '&'; ws
  e <- term
  pure (TermAst (CRef e))

cDeref :: Parser TermAst
cDeref = do
  char '*'; ws
  e <- term
  pure (TermAst (CDeref e))

cAdd :: Parser TermAst
cAdd = do
  char '('; ws
  string "+"; ws
  x <- term; ws
  y <- term; ws
  char ')'
  pure (TermAst (CAdd x y))

cSub :: Parser TermAst
cSub = do
  char '('; ws
  string "-"; ws
  x <- term; ws
  y <- term; ws
  char ')'
  pure (TermAst (CSub x y))

cLess :: Parser TermAst
cLess = do
  char '('; ws
  string "<"; ws
  x <- term; ws
  y <- term; ws
  char ')'
  pure (TermAst (CLess x y))

cGrtr :: Parser TermAst
cGrtr = do
  char '('; ws
  string ">"; ws
  x <- term; ws
  y <- term; ws
  char ')'
  pure (TermAst (CGrtr x y))

cEql :: Parser TermAst
cEql = do
  char '('; ws
  string "=="; ws
  x <- term; ws
  y <- term; ws
  char ')'
  pure (TermAst (CEql x y))

cCall :: Parser TermAst
cCall = do
  char '/'; ws
  fn <- term
  args <- fromList <$> many (ws *> term); ws
  char '\\'
  pure (TermAst (CFunCall fn args))

cFunType :: Parser TermAst
cFunType = do
  string "cfun"; ws
  ps <- try (char '(' *> ws *> char ')' *> pure Empty) <|> do
    char '('; ws
    p <- term
    ps <- fromList <$> many (char ',' *> term)
    char ')'; ws
    pure (p <| ps)
  string "->"; ws
  outTy <- term
  pure (TermAst (CFunType ps outTy))

implProp :: Parser TermAst
implProp = do
  char '('; ws
  string "impl"; ws
  p <- term; ws
  q <- term; ws
  char ')'
  pure (TermAst (ImplProp p q))

conjProp :: Parser TermAst
conjProp = do
  char '('; ws
  string "conj"; ws
  p <- term; ws
  q <- term; ws
  char ')'
  pure (TermAst (ConjProp p q))

disjProp :: Parser TermAst
disjProp = do
  char '('; ws
  string "disj"; ws
  p <- term; ws
  q <- term; ws
  char ')'
  pure (TermAst (DisjProp p q))

allProp :: Parser TermAst
allProp = try s1 <|> s2 where
  s1 :: Parser TermAst
  s1 = do
    string "all"; ws
    n <- name; ws
    char ','; ws
    body <- term
    pure (TermAst (ForallProp (TermAst (MetaLam (singleton n) body))))

  s2 :: Parser TermAst
  s2 = do
    string "all"; ws
    body <- term
    pure (TermAst (ForallProp body))

someProp :: Parser TermAst
someProp = try s1 <|> s2 where
  s1 :: Parser TermAst
  s1 = do
    string "some"; ws
    n <- name; ws
    char ','; ws
    body <- term
    pure (TermAst (ExistsProp (TermAst (MetaLam (singleton n) body))))

  s2 :: Parser TermAst
  s2 = do
    string "some"; ws
    body <- term
    pure (TermAst (ExistsProp body))

eqProp :: Parser TermAst
eqProp = do
  char '('; ws
  string "equal"; ws
  x <- term; ws
  y <- term; ws
  char ')'
  pure (TermAst (EqualProp x y))

cInt :: Parser TermAst
cInt = (TermAst . CInt . read) <$> some digitChar

term :: Parser TermAst
term = do
  pos <- getSourcePos
  e <-
    try metaLam <|>
    try objLam <|>
    try app <|>
    try metaUniv <|>
    try objUniv <|>
    try letB <|>
    try metaPiTy <|>
    try objPiTy <|>
    try liftCore <|>
    try quoteCore <|>
    try spliceCore <|>
    try liftLow <|>
    try quoteLow <|>
    try spliceLow <|>
    try liftLowStmt <|>
    try quoteLowStmt <|>
    try cIntTy <|>
    try cVoidTy <|>
    try cPtrTy <|>
    -- try cLValTy <|>
    -- try cRValTy <|>
    try cRef <|>
    try cDeref <|>
    try cAdd <|>
    try cSub <|>
    try cLess <|>
    try cGrtr <|>
    try cEql <|>
    try cCall <|>
    try cFunType <|>
    try cInt <|>
    try implProp <|>
    try conjProp <|>
    try disjProp <|>
    try allProp <|>
    try someProp <|>
    try eqProp <|>
    var
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
