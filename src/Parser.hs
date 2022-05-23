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
  [  ]

ws :: Parser ()
ws = void (many (try (char ' ') <|> try (char '\n') <|> try (char '\r') <|> char '\t'))

nameChar = (try alphaNumChar <|> char '_')

type Parser a = ParsecT Void Text (State Id) a

name :: Parser NameAst
name = do
  s <- some nameChar
  pure (NameAst (UserName (pack s)))

term = undefined

freshId :: Parser Id
freshId = do
  did <- get
  modify (+1)
  pure did

parse :: Text -> Either String TermAst
parse text =
  case
      fst .
      flip runState 0 . 
      runParserT (term >>= \e -> ws *> eof *> pure e) "<TODO>" $
      text
    of
    Right term -> Right term
    Left err -> Left (errorBundlePretty err)
