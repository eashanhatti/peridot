module Elaboration.Query where

type role Query nominal

data Query a

type role Key nominal

data Key a

query :: Key a -> Query a