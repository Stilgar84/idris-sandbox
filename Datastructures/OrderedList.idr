
module OrderedList

%default total

-- Strictly increasing list of natural
data OrderedList : (min:Nat) -> Type where
  Nil  : OrderedList 20 -- do this better...
  (::) : (k:Nat) -> OrderedList (k + S y) -> OrderedList k

merge : OrderedList ma -> OrderedList mb -> (mr**OrderedList mr) --(min ma mb)
merge [] listb = (_**listb)
merge lista [] = (_**lista)
merge (xa::ta) (xb::tb) = ?todo

testOk : OrderedList 1
testOk = 1 :: 2 :: 5 :: Nil

--testFail1 : OrderedList k
--testFail1 = 1 :: 1 :: 3 :: Nil
--
--testFail2 : OrderedList k
--testFail2 = 1 :: 4 :: 3 :: Nil

