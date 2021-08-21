module Parsing (parseTerm) where

import Text.Parsec
import Surface

type Parser = Parsec String ()

parseTerm :: String -> Either ParseError Term
parseTerm = parse (do { term <- pPrec3; eof; pure term }) ""

ws :: Parser ()
ws = do
  many1 (choice [char ' ', char '\n', char '\r', char '\t'])
  pure ()

pParens :: Parser Term
pParens = do
  char '('
  optional ws
  term <- try pPrec3 <|> try pPrec2 <|> try pPrec1 <|> pPrec0
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

pPrec3 :: Parser Term
pPrec3 = do
  pos1 <- getPosition
  term <- try pArrow <|> pPrec2
  pos2 <- getPosition
  pure $ Spanned term (Span pos1 pos2)

pPrec2 :: Parser Term
pPrec2 = do
  pos1 <- getPosition
  term <- try pAnn <|> pPrec1
  pos2 <- getPosition
  pure $ Spanned term (Span pos1 pos2)

pPrec1:: Parser Term
pPrec1 = do
  pos1 <- getPosition
  term <- try pApp <|> pPrec0
  pos2 <- getPosition
  pure $ Spanned term (Span pos1 pos2)

pPrec0 :: Parser Term
pPrec0 = do
  pos1 <- getPosition
  term <- try pVar <|> try pLam <|> try pPi <|> try pLet <|> try pUniverse <|> try pHole <|> pParens
  pos2 <- getPosition
  pure $ Spanned term (Span pos1 pos2)

pArrow :: Parser Term
pArrow = do
  inTy <- pPrec2
  optional ws
  string "->"
  optional ws
  outTy <- pPrec3
  pure $ Pi (Name "_") inTy outTy

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
  body <- pPrec3
  pure $ Lam name body

pPi :: Parser Term
pPi = do
  char '('
  optional ws
  name <- pName
  optional ws
  char ':'
  optional ws
  inTy <- pPrec3
  optional ws
  char ')'
  optional ws
  string "->"
  optional ws
  outTy <- pPrec3
  pure $ Pi name inTy outTy

pLet :: Parser Term
pLet = do
  string "let"
  ws
  name <- pName
  ws
  char ':'
  ws
  ty <- pPrec3
  ws
  char '='
  ws
  def <- pPrec3
  ws
  string "in"
  ws
  body <- pPrec3
  pure $ Let name def ty body

pUniverse :: Parser Term
pUniverse = do
  string "Type"
  pure Universe

pHole :: Parser Term
pHole = do
  char '?'
  pure Hole