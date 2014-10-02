
module Main
{- 	
foo : List Int -> List Int
foo xs = if List.length xs < 4
           then ?case_one
           else ?case_two

Main.case_one = proof
  intro
  exact (List.reverse xs)
 	

case_one_proof : (l : List Int)
              -> (length l < 4) = True
              -> foo l = reverse l
case_one_proof = ?qsdf

Main.qsdf = proof
  intro
  intro H
  rewrite (sym H)
  compute
  trivial

main : IO ()
main = putStrLn $ show $ foo [1,2,3]

-}


breakAWord : Nat -> String -> List (List Char)
breakAWord n s = go2 s (go n n) where
	go : Nat -> Nat -> String -> (String, List Char)
	go n _ ""     = ("", [])
	go n Z s     = (s, [])
	go n (S r) s = let (rs, ra) = go n r (strTail s) in (rs, (strHead s):: ra)

	go2 : String -> (String -> (String, List Char)) -> List (List Char)
	go2 s f with (f s)
		| ("", ra) = [ra]
		| (rs, ra) = ra :: go2 rs f


breakWords : Nat -> String -> List (List Char)
breakWords n s = concat $ map (breakAWord n) (words s)

data
  SplitBy : Type -> Nat -> Type
where
  Split :  (vs : List (Vect n a))
        -> (m : Nat) -> (LT m n)
        -> (v : Vect m a)
        -> SplitBy a n

--split_up : (n:Nat) -> (Vect a m) -> SplitBy a (S n)

add_elm : Vect n a -> SplitBy a n -> SplitBy a n
 	add_elm v (Split vs a b c) = Split (v::vs) a b c

{-
simple_split_up : (n:Nat) -> (Vect a m) -> SplitBy a (S n)
simple_split_up n {m} xs with (compare m (S n))
  | LT = Split [] m ?case1_pf xs
  | _  = add_elm (take (S n) xs) $ split_up n (drop (S n) xs)

-}

total
groupBy : Nat -> (List String) -> String -> (List String)
groupBy n [] s = 
	if length s > n then ?todoBreakWord else [s]
groupBy n (xs :: l) s =
	if (length xs) + (length s) > n then
		s :: xs :: l
	else
		(xs++s)::l
		

myWrap : Nat -> String -> String
myWrap n s = concat (reverse (foldl (groupBy n) [] (words s)))


tests : (Nat -> String -> String) -> List Bool
tests wrap = [ wrap 1 ""   == ""
             , wrap 1 "x"  == "x"
             , wrap 1 "xx" == "x\nx"
             , wrap 1 "xxx" == "x\nx\nx"
             , wrap 1 "x x" == "x\nx"
             , wrap 2 "x x" == "x\nx"
             , wrap 3 "x xxxx" == "x\nxxx\nx"
             ]


{-

data User = MkUser String

data Redeem = MkRedeem Int

data Earn = Recommend User

Action : Type
Action = Either Redeem Earn

data History : Type where
  MkHist :  (user     : User)               ->
            (redeemed : Nat)                ->
            (offset   : Nat)                ->
            (earned   : Nat)                ->
            LTE (redeemed + offset) earned  ->
            Vect (redeemed + earned) Action ->
            History

recommendApp : History -> User -> History
recommendApp (MkHist u r o e p v) friend =
  MkHist u r (S o) (S e) ?wtf v'
    where a  : Action
          a  = Right $ Recommend friend
          v' : Vect (r + (S e)) Action
          v' = rewrite (sym $ plusSuccRightSucc r e) in a :: v

redeemToken : History -> Redeem -> Maybe History
redeemToken (MkHist _ _ Z     _ _ _) _     = Nothing
redeemToken (MkHist u r (S o) e p v) token =
  Just $ MkHist u (S r) o e ?redeemPrf (Left token :: v)
-}
{-

import Decidable.Order

inBounds : Nat -> Type
inBounds x = NatLTE  x 10

inBounds2 : Nat -> Type
inBounds2 x = NatLTE  x 5

--NatLTEIsTransitive
--LT 5 10

toTest : (x:Nat) -> inBounds2 x -> NatLTE 5 10 -> inBounds x
toTest x = NatLTEIsTransitive x 5 10



toTest2 : (x < 10) || (x > 5) = True
toTest2 = ?basic

toTest3 : (5 < 10) = True
toTest3 = ?triv

toTest4 : (x : Nat) -> (x < 10) || (x > 5) = True
toTest4 x = case x<10 of
	True => ?basicLt10
	False => ?basicGt10


toTest5 : (x : Nat) -> (x < 10) || (x > 5) = True
toTest5 x | (x<10) = ?basicLt10b
toTest5 x | (not x<10) = ?basicGe10b


drawPoint : (x : Int) -> so (inBounds x) -> Int
drawPoint x p = 2*x

drawPoint2 : (x : Int) -> so (inBounds2 x) -> Int
drawPoint2 x p = drawPoint x oh


anInt : Int
anInt = 8

--test4 : IO ()
--test4 = do
--	x <- return anInt
--	case choose (inBounds2 x) of
--		Left p => print $ drawPoint x p
--		Right p => print 1



---------- Proofs ----------

Main.redeemPrf = proof
  compute
  intro
  intro
  intro
  intro
  rewrite plusSuccRightSucc r o
  intros
  trivial


Main.wtf = proof
  intros
  rewrite (plusSuccRightSucc r o)
  mrefine lteSucc
  trivial

-}

