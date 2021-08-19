module Parsing (parseTerm) where

import Text.Parsec
import Surface

type Parser = Parsec String ()

parseTerm :: String -> Either ParseError Term
parseTerm = parse (do { term <- pPrec2; eof; pure term }) ""

ws :: Parser ()
ws = do
  many1 (choice [char ' ', char '\n', char '\r', char '\t'])
  pure ()

pParens :: Parser Term
pParens = do
  char '('
  optional ws
  term <- try pPrec2 <|> try pPrec1 <|> pPrec0
  optional ws
  char ')'
  pure term

keyword x = x `elem` ["let", "in", "Type", ":", "=", "->", "=>"]

pName :: Parser Name
pName = do
  name <- many1 alphaNum
  if keyword name
  then unexpected "keyword"
  else pure $ Name name

pPrec2 :: Parser Term
pPrec2 = do
  pos1 <- getPosition
  term <- try pAnn <|> pPrec1
  pos2 <- getPosition
  pure $ Spanned term (Span pos1 pos2)

pPrec1:: Parser Term
pPrec1 = try pApp <|> pPrec0

pPrec0 :: Parser Term
pPrec0 = try pVar <|> try pLam <|> try pPi <|> try pLet <|> try pUniverse <|> try pHole <|> pParens

pAnn :: Parser Term
pAnn = do
  term <- pPrec1
  ws
  char ':'
  ws
  ty <- pPrec1
  pure $ Ann term ty

pApp :: Parser Term
pApp = do
  lam <- pPrec0
  ws
  args <- pPrec0 `sepBy1` ws
  pure $ app lam args
  where
    app lam args = case reverse args of
      (arg:args) -> App (app lam args) arg
      [] -> lam

pVar :: Parser Term
pVar = do
  name <- pName
  pure $ Var name

pLam :: Parser Term
pLam = do
  char '\\'
  optional ws
  name <- pName
  optional ws
  string "=>"
  optional ws
  body <- pPrec2
  pure $ Lam name body

pPi :: Parser Term
pPi = do
  char '('
  optional ws
  name <- pName
  optional ws
  char ':'
  optional ws
  inTy <- pPrec2
  optional ws
  char ')'
  optional ws
  string "->"
  optional ws
  outTy <- pPrec2
  pure $ Pi name inTy outTy

pLet :: Parser Term
pLet = do
  string "let"
  ws
  name <- pName
  ws
  char ':'
  ws
  ty <- pPrec2
  ws
  char '='
  ws
  def <- pPrec2
  ws
  string "in"
  ws
  body <- pPrec2
  pure $ Let name def ty body

pUniverse :: Parser Term
pUniverse = do
  string "Type"
  pure Universe

pHole :: Parser Term
pHole = do
  char '?'
  pure Hole