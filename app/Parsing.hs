{-# OPTIONS_GHC -w #-}
module Parsing(parseTerm, lex) where

import Surface
import Prelude hiding (lex)
import Data.Char(isAlphaNum)
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.0

data HappyAbsSyn t4 t5 t6
	= HappyTerminal (Token)
	| HappyErrorToken Prelude.Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,74) ([27712,25090,19,64,0,8192,0,45312,9,64,0,0,0,0,50176,38,64,64,0,256,25088,19,32768,1240,9924,0,45312,9,0,0,128,128,55424,4,8208,310,2,19848,0,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_parseTerm","Prec3","Prec2","Prec1","let","in","':'","'='","type","'('","')'","'\\\\'","'?'","'=>'","'->'","name","%eof"]
        bit_start = st Prelude.* 19
        bit_end = (st Prelude.+ 1) Prelude.* 19
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..18]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (7) = happyShift action_4
action_0 (11) = happyShift action_5
action_0 (12) = happyShift action_6
action_0 (14) = happyShift action_7
action_0 (15) = happyShift action_8
action_0 (18) = happyShift action_9
action_0 (4) = happyGoto action_10
action_0 (5) = happyGoto action_11
action_0 (6) = happyGoto action_3
action_0 _ = happyFail (happyExpListPerState 0)

action_1 (7) = happyShift action_4
action_1 (11) = happyShift action_5
action_1 (12) = happyShift action_6
action_1 (14) = happyShift action_7
action_1 (15) = happyShift action_8
action_1 (18) = happyShift action_9
action_1 (5) = happyGoto action_2
action_1 (6) = happyGoto action_3
action_1 _ = happyFail (happyExpListPerState 1)

action_2 (17) = happyShift action_12
action_2 _ = happyFail (happyExpListPerState 2)

action_3 (9) = happyShift action_17
action_3 _ = happyReduce_4

action_4 (18) = happyShift action_16
action_4 _ = happyFail (happyExpListPerState 4)

action_5 _ = happyReduce_9

action_6 (7) = happyShift action_4
action_6 (11) = happyShift action_5
action_6 (12) = happyShift action_6
action_6 (14) = happyShift action_7
action_6 (15) = happyShift action_8
action_6 (18) = happyShift action_15
action_6 (4) = happyGoto action_14
action_6 (5) = happyGoto action_11
action_6 (6) = happyGoto action_3
action_6 _ = happyFail (happyExpListPerState 6)

action_7 (18) = happyShift action_13
action_7 _ = happyFail (happyExpListPerState 7)

action_8 _ = happyReduce_10

action_9 _ = happyReduce_5

action_10 (19) = happyAccept
action_10 _ = happyFail (happyExpListPerState 10)

action_11 (17) = happyShift action_12
action_11 _ = happyReduce_2

action_12 (7) = happyShift action_4
action_12 (11) = happyShift action_5
action_12 (12) = happyShift action_6
action_12 (14) = happyShift action_7
action_12 (15) = happyShift action_8
action_12 (18) = happyShift action_9
action_12 (4) = happyGoto action_23
action_12 (5) = happyGoto action_11
action_12 (6) = happyGoto action_3
action_12 _ = happyFail (happyExpListPerState 12)

action_13 (16) = happyShift action_22
action_13 _ = happyFail (happyExpListPerState 13)

action_14 (13) = happyShift action_21
action_14 _ = happyFail (happyExpListPerState 14)

action_15 (9) = happyShift action_20
action_15 _ = happyReduce_5

action_16 (9) = happyShift action_19
action_16 _ = happyFail (happyExpListPerState 16)

action_17 (7) = happyShift action_4
action_17 (11) = happyShift action_5
action_17 (12) = happyShift action_6
action_17 (14) = happyShift action_7
action_17 (15) = happyShift action_8
action_17 (18) = happyShift action_9
action_17 (5) = happyGoto action_18
action_17 (6) = happyGoto action_3
action_17 _ = happyFail (happyExpListPerState 17)

action_18 _ = happyReduce_3

action_19 (7) = happyShift action_4
action_19 (11) = happyShift action_5
action_19 (12) = happyShift action_6
action_19 (14) = happyShift action_7
action_19 (15) = happyShift action_8
action_19 (18) = happyShift action_9
action_19 (4) = happyGoto action_26
action_19 (5) = happyGoto action_11
action_19 (6) = happyGoto action_3
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (7) = happyShift action_4
action_20 (11) = happyShift action_5
action_20 (12) = happyShift action_6
action_20 (14) = happyShift action_7
action_20 (15) = happyShift action_8
action_20 (18) = happyShift action_9
action_20 (4) = happyGoto action_25
action_20 (5) = happyGoto action_11
action_20 (6) = happyGoto action_3
action_20 _ = happyFail (happyExpListPerState 20)

action_21 _ = happyReduce_11

action_22 (7) = happyShift action_4
action_22 (11) = happyShift action_5
action_22 (12) = happyShift action_6
action_22 (14) = happyShift action_7
action_22 (15) = happyShift action_8
action_22 (18) = happyShift action_9
action_22 (4) = happyGoto action_24
action_22 (5) = happyGoto action_11
action_22 (6) = happyGoto action_3
action_22 _ = happyFail (happyExpListPerState 22)

action_23 _ = happyReduce_1

action_24 _ = happyReduce_6

action_25 (13) = happyShift action_28
action_25 _ = happyFail (happyExpListPerState 25)

action_26 (10) = happyShift action_27
action_26 _ = happyFail (happyExpListPerState 26)

action_27 (7) = happyShift action_4
action_27 (11) = happyShift action_5
action_27 (12) = happyShift action_6
action_27 (14) = happyShift action_7
action_27 (15) = happyShift action_8
action_27 (18) = happyShift action_9
action_27 (4) = happyGoto action_30
action_27 (5) = happyGoto action_11
action_27 (6) = happyGoto action_3
action_27 _ = happyFail (happyExpListPerState 27)

action_28 (17) = happyShift action_29
action_28 _ = happyFail (happyExpListPerState 28)

action_29 (7) = happyShift action_4
action_29 (11) = happyShift action_5
action_29 (12) = happyShift action_6
action_29 (14) = happyShift action_7
action_29 (15) = happyShift action_8
action_29 (18) = happyShift action_9
action_29 (4) = happyGoto action_32
action_29 (5) = happyGoto action_11
action_29 (6) = happyGoto action_3
action_29 _ = happyFail (happyExpListPerState 29)

action_30 (8) = happyShift action_31
action_30 _ = happyFail (happyExpListPerState 30)

action_31 (7) = happyShift action_4
action_31 (11) = happyShift action_5
action_31 (12) = happyShift action_6
action_31 (14) = happyShift action_7
action_31 (15) = happyShift action_8
action_31 (18) = happyShift action_9
action_31 (4) = happyGoto action_33
action_31 (5) = happyGoto action_11
action_31 (6) = happyGoto action_3
action_31 _ = happyFail (happyExpListPerState 31)

action_32 _ = happyReduce_7

action_33 _ = happyReduce_8

happyReduce_1 = happySpecReduce_3  4 happyReduction_1
happyReduction_1 (HappyAbsSyn4  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn4
		 (Pi (Name "_") happy_var_1 happy_var_3
	)
happyReduction_1 _ _ _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_1  4 happyReduction_2
happyReduction_2 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn4
		 (happy_var_1
	)
happyReduction_2 _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_3  5 happyReduction_3
happyReduction_3 (HappyAbsSyn5  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn5
		 (Ann happy_var_1 happy_var_3
	)
happyReduction_3 _ _ _  = notHappyAtAll 

happyReduce_4 = happySpecReduce_1  5 happyReduction_4
happyReduction_4 (HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn5
		 (happy_var_1
	)
happyReduction_4 _  = notHappyAtAll 

happyReduce_5 = happySpecReduce_1  6 happyReduction_5
happyReduction_5 (HappyTerminal (TName happy_var_1))
	 =  HappyAbsSyn6
		 (Var (Name happy_var_1)
	)
happyReduction_5 _  = notHappyAtAll 

happyReduce_6 = happyReduce 4 6 happyReduction_6
happyReduction_6 ((HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TName happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (Lam (Name happy_var_2) happy_var_4
	) `HappyStk` happyRest

happyReduce_7 = happyReduce 7 6 happyReduction_7
happyReduction_7 ((HappyAbsSyn4  happy_var_7) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TName happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (Pi (Name happy_var_2) happy_var_4 happy_var_7
	) `HappyStk` happyRest

happyReduce_8 = happyReduce 8 6 happyReduction_8
happyReduction_8 ((HappyAbsSyn4  happy_var_8) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TName happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (Let (Name happy_var_2) happy_var_4 happy_var_6 happy_var_8
	) `HappyStk` happyRest

happyReduce_9 = happySpecReduce_1  6 happyReduction_9
happyReduction_9 _
	 =  HappyAbsSyn6
		 (Universe
	)

happyReduce_10 = happySpecReduce_1  6 happyReduction_10
happyReduction_10 _
	 =  HappyAbsSyn6
		 (Hole
	)

happyReduce_11 = happySpecReduce_3  6 happyReduction_11
happyReduction_11 _
	(HappyAbsSyn4  happy_var_2)
	_
	 =  HappyAbsSyn6
		 (happy_var_2
	)
happyReduction_11 _ _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 19 19 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	TLet -> cont 7;
	TIn -> cont 8;
	TColon -> cont 9;
	TEquals -> cont 10;
	TUniv -> cont 11;
	TOpenParen -> cont 12;
	TCloseParen -> cont 13;
	TBackslash -> cont 14;
	THole -> cont 15;
	TFatArrow -> cont 16;
	TThinArrow -> cont 17;
	TName happy_dollar_dollar -> cont 18;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 19 tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

newtype HappyIdentity a = HappyIdentity a
happyIdentity = HappyIdentity
happyRunIdentity (HappyIdentity a) = a

instance Prelude.Functor HappyIdentity where
    fmap f (HappyIdentity a) = HappyIdentity (f a)

instance Applicative HappyIdentity where
    pure  = HappyIdentity
    (<*>) = ap
instance Prelude.Monad HappyIdentity where
    return = pure
    (HappyIdentity p) >>= q = q p

happyThen :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
happyThen = (Prelude.>>=)
happyReturn :: () => a -> HappyIdentity a
happyReturn = (Prelude.return)
happyThen1 m k tks = (Prelude.>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> HappyIdentity a
happyReturn1 = \a tks -> (Prelude.return) a
happyError' :: () => ([(Token)], [Prelude.String]) -> HappyIdentity a
happyError' = HappyIdentity Prelude.. (\(tokens, _) -> parseError tokens)
parseTerm tks = happyRunIdentity happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


parseError :: [Token] -> a
parseError _ = error "Parse error"

data Token
  = TLet
  | TIn
  | TColon
  | TEquals
  | TUniv
  | TOpenParen
  | TCloseParen
  | TBackslash
  | THole
  | TFatArrow
  | TThinArrow
  | TName String
  deriving Show

lex :: String -> [Token]
lex s = case s of
  'l':'e':'t':s -> TLet:(lex s)
  'i':'n':s -> TIn:(lex s)
  ':':s -> TColon:(lex s)
  '=':s -> TEquals:(lex s)
  'T':'y':'p':'e':s -> TUniv:(lex s)
  '(':s -> TOpenParen:(lex s)
  ')':s -> TCloseParen:(lex s)
  '\\':s -> TBackslash:(lex s)
  '?':s -> THole:(lex s)
  '=':'>':s -> TFatArrow:(lex s)
  '-':'>':s -> TThinArrow:(lex s)
  ' ':s -> lex s
  '\n':s -> lex s
  '\r':s -> lex s
  '\t':s -> lex s
  c:s | isAlphaNum c -> lexVar s [c]
  [] -> []

lexVar :: String -> String -> [Token]
lexVar s a = case s of
  c:s ->
    if isAlphaNum c then
      lexVar s (c:a)
    else
      (TName a):(lex s)
  [] -> []
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $










































data Happy_IntList = HappyCons Prelude.Int Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action









































indexShortOffAddr arr off = arr Happy_Data_Array.! off


{-# INLINE happyLt #-}
happyLt x y = (x Prelude.< y)






readArrayBit arr bit =
    Bits.testBit (indexShortOffAddr arr (bit `Prelude.div` 16)) (bit `Prelude.mod` 16)






-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Prelude.Int ->                    -- token number
         Prelude.Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Prelude.- ((1) :: Prelude.Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             _ = nt :: Prelude.Int
             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n Prelude.- ((1) :: Prelude.Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Prelude.- ((1)::Prelude.Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction









happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ((HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.









{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
