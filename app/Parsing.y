{
module Parsing(parseTerm, lex) where

import Surface
import Prelude hiding (lex)
import Data.Char(isAlphaNum)
import Data.Map(fromList)
}

%name parseTerm Prec3
%tokentype { Token }
%error { parseError }

%token
  "let"     { TLet }
  "in"      { TIn }
  "Code"    { TQuoteTy }
  "ind"     { TInd }
  "of"      { TOf }
  "splice"  { TSplice }
  "quote"   { TQuote }
  ":"       { TColon }
  "="       { TEquals }
  "Ty0"     { TUniv0 }
  "Ty1"     { TUniv1 }
  "("       { TOpenParen }
  ")"       { TCloseParen }
  "["       { TOpenBracket }
  "]"       { TCloseBracket }
  "\\"      { TBackslash }
  "?"       { THole }
  "=>"      { TFatArrow }
  "->"      { TThinArrow }
  ","       { TComma }
  "end"     { TEnd }
  name      { TName $$ }

%%

Prec3
  : Prec2 "->" Prec3                          { Pi (Name undefined) $1 $3 }
  | Prec2                                     { $1 }

Prec2
  : Prec1 ":" Prec2                           { Ann $1 $3 }
  | Prec1                                     { $1 }

Prec1
  : Prec1 Prec0                               { App $1 $2 }
  | Prec0                                     { $1 }

Prec0
  : name                                      { Var (Name $1) }
  | "\\" NameList "->" Prec3                  { foldr (\name body -> Lam (Name name) body) $4 $2 }
  | "\\" name "->" Prec3                      { Lam (Name $2) $4 }
  | "(" name ":" Prec3 ")" "->" Prec3         { Pi (Name $2) $4 $7 }
  | "let" name "=" Prec3 "in" Prec3           { Let (Name $2) $4 Hole $6 }
  | "let" name ":" Prec3 "=" Prec3 "in" Prec3 { Let (Name $2) $6 $4 $8 }
  | "Code" Prec0                              { Code $2 }
  | "quote" Prec3                             { Quote $2 }
  | "splice" Prec3                            { Splice $2 }
  | "Ty0"                                     { U0 }
  | "Ty1"                                     { U1 }
  | "?"                                       { Hole }
  | Parens                                    { $1 }

NameList
  : name                                      { [$1] }
  | name NameList                             { [$1] ++ $2 }

Parens
  : "(" Prec3 ")"                             { $2 }
  | "(" Prec2 ")"                             { $2 }
  | "(" Prec1 ")"                             { $2 }
  | "(" Prec0 ")"                             { $2 }

{
parseError :: [Token] -> a
parseError tokens = error $ show tokens

data Token
  = TLet
  | TIn
  | TColon
  | TEquals
  | TUniv0
  | TUniv1
  | TOpenParen
  | TCloseParen
  | TBackslash
  | THole
  | TFatArrow
  | TThinArrow
  | TName String
  | TQuoteTy
  | TQuote
  | TInd
  | TComma
  | TOf
  | TEnd
  | TSplice
  | TOpenBracket
  | TCloseBracket
  deriving Show

lex :: String -> [Token]
lex s = case s of
  'e':'n':'d':s -> TEnd:(lex s)
  'i':'n':'d':s -> TInd:(lex s)
  'o':'f':s -> TOf:(lex s)
  'l':'e':'t':s -> TLet:(lex s)
  'i':'n':s -> TIn:(lex s)
  'C':'o':'d':'e':s -> TQuoteTy:(lex s)
  'q':'u':'o':'t':'e':s -> TQuote:(lex s)
  's':'p':'l':'i':'c':'e':s -> TSplice:(lex s)
  ':':s -> TColon:(lex s)
  '=':'>':s -> TFatArrow:(lex s)
  '=':s -> TEquals:(lex s)
  'T':'y':'0':s -> TUniv0:(lex s)
  'T':'y':'1':s -> TUniv1:(lex s)
  'S':s -> TQuoteTy:(lex s)
  '[':s -> TOpenBracket:(lex s)
  ']':s -> TCloseBracket:(lex s)
  '(':s -> TOpenParen:(lex s)
  ')':s -> TCloseParen:(lex s)
  '\\':s -> TBackslash:(lex s)
  '?':s -> THole:(lex s)
  '-':'>':s -> TThinArrow:(lex s)
  ',':s -> TComma:(lex s)
  ' ':s -> lex s
  '\n':s -> lex s
  '\r':s -> lex s
  '\t':s -> lex s
  c:s | isAlphaNum c -> lexVar s [c]
  [] -> []
  _ -> error $ "'" ++ s ++ "'"

lexVar :: String -> String -> [Token]
lexVar s a = case s of
  c:s ->
    if isAlphaNum c || c == '_' then
      lexVar s (c:a)
    else
      (TName $ reverse a):(lex (c:s))
  [] -> (TName $ reverse a):[]
}