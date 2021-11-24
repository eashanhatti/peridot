module Etc where

import Debug.Trace

tr s f = trace s () `seq` f