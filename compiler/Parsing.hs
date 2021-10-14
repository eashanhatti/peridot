module Parsing where

import Surface
import Data.Binary

getWord16 = get :: Get Word16
getCharacter = get :: Get Char

parseString :: Get String
parseString = do
  len <- getWord16
  loop len
  where
    loop n = case n of
      0 -> pure []
      n -> do
        c <- getCharacter
        cs <- loop $ n - 1
        pure $ c:cs

parseStrings n = case n of
  0 -> pure []
  n -> do
    s <- parseString
    ss <- parseStrings $ n - 1
    pure $ s:ss

parseTerm :: Get Term 
parseTerm = do
  tag <- getWord8
  case tag of
    0 -> parseString >>= pure . Var . Name
    1 -> do
      len <- getWord16
      gname <- parseStrings len
      pure $ GVar (GName gname)
    2 -> do
      len <- getWord16
      names <- parseStrings len
      body <- parseTerm
      pure $ Lam (map Name names) body
    3 -> do
      lam <- parseTerm
      len <- getWord16
      args <- loop len
      pure $ App lam args
      where
        loop n = case n of
          0 -> pure []
          n -> do
            a <- parseTerm
            as <- loop $ n - 1
            pure $ a:as
    4 -> do
      term <- parseTerm
      ty <- parseTerm
      pure $ Ann term ty
    5 -> do
      name <- parseString
      inTy <- parseTerm
      outTy <- parseTerm
      pure $ Pi (Name name) inTy outTy
    6 -> do
      name <- parseString
      def <- parseTerm
      defTy <- parseTerm
      body <- parseTerm
      pure $ Let (Name name) def defTy body
    7 -> pure U1
    8 -> pure U0
    9 -> parseTerm >>= pure . Code
    10 -> parseTerm >>= pure . Quote
    11 -> parseTerm >>= pure . Splice
    12 -> pure Hole

parseItem :: Get Item
parseItem = do
  tag <- getWord8
  case tag of
    0 -> do
      name <- parseString
      len <- getWord16
      items <- loop len
      pure $ NamespaceDef (Name name) items
      where
        loop n = case n of
          0 -> pure []
          n -> do
            i <- parseItem
            is <- loop $ n - 1
            pure $ i:is
    1 -> do
      name <- parseString
      dec <- parseTerm
      def <- parseTerm
      pure $ TermDef (Name name) dec def
    2 -> do
      name <- parseString
      dec <- parseTerm
      len <- getWord16
      cons <- loop len
      pure $ IndDef (Name name) dec cons
      where
        loop n = case n of
          0 -> pure []
          n -> do
            name <- parseString
            ty <- parseTerm
            cs <- loop $ n - 1
            pure $ (Name name, ty):cs

instance Binary Item where
  get = parseItem
  put = undefined