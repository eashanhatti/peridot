{-# LANGUAGE BlockArguments #-}

module Parsing where

import Surface
import Data.Binary
import Control.Monad(replicateM)

getWord16 = get :: Get Word16
getCharacter = get :: Get Char

getString :: Get String
getString = do
  len <- getWord16
  loop len
  where
    loop n = case n of
      0 -> pure []
      n -> do
        c <- getCharacter
        cs <- loop $ n - 1
        pure $ c:cs

getStrings n = replicateM n getString

getTerm :: Get Term 
getTerm = do
  tag <- getWord8
  case tag of
    0 -> getString >>= pure . Var . Name
    1 -> do
      len <- getWord16
      gname <- getStrings (fromIntegral len)
      pure $ GVar (GName gname)
    2 -> do
      len <- getWord16
      names <- getStrings (fromIntegral len)
      body <- getTerm
      pure $ Lam (map Name names) body
    3 -> do
      lam <- getTerm
      len <- getWord16
      args <- replicateM (fromIntegral len) getTerm
      pure $ App lam args
    4 -> do
      term <- getTerm
      ty <- getTerm
      pure $ Ann term ty
    5 -> do
      name <- getString
      inTy <- getTerm
      outTy <- getTerm
      pure $ Pi (Name name) inTy outTy
    6 -> do
      name <- getString
      def <- getTerm
      defTy <- getTerm
      body <- getTerm
      pure $ Let (Name name) def defTy body
    7 -> pure U1
    8 -> pure U0
    9 -> getTerm >>= pure . Code
    10 -> getTerm >>= pure . Quote
    11 -> getTerm >>= pure . Splice
    12 -> pure Hole
    13 -> do
      ty <- getTerm
      len <- getWord16
      args <- replicateM (fromIntegral len) getTerm
      pure $ MkProd ty args

getItem :: Get Item
getItem = do
  tag <- getWord8
  case tag of
    0 -> do
      name <- getString
      len <- getWord16
      items <- replicateM (fromIntegral len) getItem
      pure $ NamespaceDef (Name name) items
    1 -> do
      name <- getString
      dec <- getTerm
      def <- getTerm
      pure $ TermDef (Name name) dec def
    2 -> do
      name <- getString
      dec <- getTerm
      len <- getWord16
      cons <- replicateM (fromIntegral len) do
        name <- getString
        ty <- getTerm
        pure $ (Name name, ty)
      pure $ IndDef (Name name) dec cons
    3 -> do
      name <- getString
      dec <- getTerm
      len <- getWord16
      fields <- replicateM (fromIntegral len) getTerm
      pure $ ProdDef (Name name) dec fields

instance Binary Item where
  get = getItem
  put = undefined